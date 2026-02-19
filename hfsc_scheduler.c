/********************************************************************
 * HFSC Scheduler - Core Implementation v1.4
 * 
 * CRITICAL FIXES in v1.4:
 * - Cross-branch virtual time synchronization
 * - Proper VT initialization when activating from inactive branches
 * - Parent VT update to reflect active children's VT range
 ********************************************************************/

#include "hfsc_scheduler.h"
#include <rte_malloc.h>
#include <rte_log.h>
#include <rte_memory.h>
#include <string.h>
#include <math.h>

#define RTE_LOGTYPE_HFSC RTE_LOGTYPE_USER1

#define HFSC_LOG(level, fmt, args...) \
    RTE_LOG(level, HFSC, "[HFSC] " fmt, ##args)

#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

#define min(a, b) ((a) < (b) ? (a) : (b))
#define max(a, b) ((a) > (b) ? (a) : (b))

#if RTE_VERSION < RTE_VERSION_NUM(20, 11, 0, 0)
#error "HFSC requires DPDK 20.11 or newer for rte_ring_peek support"
#endif

static inline bool time_after(uint64_t a, uint64_t b)
{
    return (int64_t)(a - b) > 0;
}

static inline bool time_before(uint64_t a, uint64_t b)
{
    return time_after(b, a);
}

static inline bool time_after_eq(uint64_t a, uint64_t b)
{
    return (int64_t)(a - b) >= 0;
}

static inline bool time_before_eq(uint64_t a, uint64_t b)
{
    return time_after_eq(b, a);
}

static inline uint64_t hfsc_rate_to_sm(uint64_t rate, uint64_t tsc_hz)
{
    if (rate == 0) return 0;
    
    __uint128_t numerator = (__uint128_t)rate << HFSC_SM_SHIFT;
    uint64_t result = (uint64_t)(numerator / tsc_hz);
    
    if (result == 0 && rate > 0) return 1;
    return result;
}

static inline uint64_t hfsc_us_to_cycles(uint64_t us, uint64_t tsc_hz)
{
    return (us * tsc_hz) / 1000000ULL;
}

static inline uint64_t hfsc_get_time(void)
{
    return rte_get_tsc_cycles();
}

static inline uint64_t hfsc_sc_x2y(const hfsc_internal_sc_t *isc, uint64_t x)
{
    uint64_t dx, y;
    
    if (x <= isc->x) return isc->y;
    
    dx = x - isc->x;
    
    if (dx <= isc->dx) {
        y = isc->y + ((dx * isc->sm1) >> HFSC_SM_SHIFT);
    } else {
        y = isc->y + isc->dy + (((dx - isc->dx) * isc->sm2) >> HFSC_SM_SHIFT);
    }
    
    return y;
}

static inline uint64_t hfsc_sc_y2x(const hfsc_internal_sc_t *isc, uint64_t y)
{
    uint64_t dy, x;
    
    if (y <= isc->y) return isc->x;
    
    dy = y - isc->y;
    
    if (dy <= isc->dy) {
        if (isc->sm1 == 0) return isc->x + isc->dx;
        x = isc->x + ((dy << HFSC_SM_SHIFT) / isc->sm1);
    } else {
        if (isc->sm2 == 0) return UINT64_MAX;
        x = isc->x + isc->dx + (((dy - isc->dy) << HFSC_SM_SHIFT) / isc->sm2);
    }
    
    return x;
}

static void hfsc_init_sc(hfsc_internal_sc_t *isc, const hfsc_service_curve_t *sc,
                         uint64_t cur_time, uint64_t cur_bytes, uint64_t tsc_hz)
{
    isc->x = cur_time;
    isc->y = cur_bytes;
    
    if (sc == NULL || (sc->m1 == 0 && sc->m2 == 0)) {
        isc->dx = 0;
        isc->dy = 0;
        isc->sm1 = 0;
        isc->sm2 = 0;
        return;
    }
    
    isc->sm1 = hfsc_rate_to_sm(sc->m1, tsc_hz);
    isc->sm2 = hfsc_rate_to_sm(sc->m2, tsc_hz);
    isc->dx = hfsc_us_to_cycles(sc->d, tsc_hz);
    isc->dy = (isc->dx * isc->sm1) >> HFSC_SM_SHIFT;
}

static void hfsc_update_sc(hfsc_internal_sc_t *isc, const hfsc_service_curve_t *sc,
                           uint64_t cur_time, uint64_t cur_bytes, uint64_t tsc_hz)
{
    uint64_t sm1, sm2, dx, dy, y1, y2;
    
    if (sc == NULL || (sc->m1 == 0 && sc->m2 == 0)) return;
    
    sm1 = hfsc_rate_to_sm(sc->m1, tsc_hz);
    sm2 = hfsc_rate_to_sm(sc->m2, tsc_hz);
    dx = hfsc_us_to_cycles(sc->d, tsc_hz);
    dy = (dx * sm1) >> HFSC_SM_SHIFT;
    
    y1 = hfsc_sc_x2y(isc, cur_time);
    y2 = hfsc_sc_x2y(isc, cur_time + dx);
    
    if (sm1 <= sm2) {
        if (y1 < cur_bytes) return;
        
        isc->x = cur_time;
        isc->y = cur_bytes;
        isc->dx = dx;
        isc->dy = dy;
        isc->sm1 = sm1;
        isc->sm2 = sm2;
    } else {
        if (y2 <= cur_bytes + dy) return;
        
        if (y1 > cur_bytes) {
            uint64_t diff = y1 - cur_bytes;
            uint64_t dsm = sm1 - sm2;
            uint64_t new_dx;
            
            if (dsm == 0) {
                new_dx = dx;
            } else {
                new_dx = (diff << HFSC_SM_SHIFT) / dsm;
                if (new_dx > dx) new_dx = dx;
            }
            
            isc->x = cur_time;
            isc->y = cur_bytes;
            isc->dx = new_dx;
            isc->dy = (new_dx * sm1) >> HFSC_SM_SHIFT;
            isc->sm1 = sm1;
            isc->sm2 = sm2;
        }
    }
}

static void hfsc_init_eligible(hfsc_internal_sc_t *el, const hfsc_internal_sc_t *dl,
                               const hfsc_service_curve_t *rsc, uint64_t tsc_hz)
{
    *el = *dl;
    
    if (rsc && rsc->m1 <= rsc->m2) {
        el->dx = 0;
        el->dy = 0;
        el->sm1 = hfsc_rate_to_sm(rsc->m2, tsc_hz);
        el->sm2 = el->sm1;
    }
}

static inline void heap_swap(hfsc_class_t **heap, int i, int j)
{
    hfsc_class_t *tmp = heap[i];
    heap[i] = heap[j];
    heap[j] = tmp;
    heap[i]->rt_index = i;
    heap[j]->rt_index = j;
}

static void heap_sift_up(hfsc_class_t **heap, int pos)
{
    while (pos > 0) {
        int parent = (pos - 1) / 2;
        if (heap[pos]->cl_d >= heap[parent]->cl_d) break;
        heap_swap(heap, pos, parent);
        pos = parent;
    }
}

static void heap_sift_down(hfsc_class_t **heap, int size, int pos)
{
    while (1) {
        int left = 2 * pos + 1;
        int right = 2 * pos + 2;
        int smallest = pos;
        
        if (left < size && heap[left]->cl_d < heap[smallest]->cl_d)
            smallest = left;
        if (right < size && heap[right]->cl_d < heap[smallest]->cl_d)
            smallest = right;
        
        if (smallest == pos) break;
        
        heap_swap(heap, pos, smallest);
        pos = smallest;
    }
}

static void heap_insert(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    if (cl->rt_index >= 0) return;
    
    if (sched->rt_heap_size >= sched->rt_heap_capacity) {
        HFSC_LOG(ERR, "RT heap full\n");
        return;
    }
    
    cl->rt_index = sched->rt_heap_size;
    sched->rt_heap[sched->rt_heap_size] = cl;
    sched->rt_heap_size++;
    
    heap_sift_up(sched->rt_heap, cl->rt_index);
}

static void heap_remove(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    int pos = cl->rt_index;
    
    if (pos < 0 || pos >= (int)sched->rt_heap_size) return;
    
    sched->rt_heap_size--;
    if (pos == (int)sched->rt_heap_size) {
        cl->rt_index = -1;
        return;
    }
    
    sched->rt_heap[pos] = sched->rt_heap[sched->rt_heap_size];
    sched->rt_heap[pos]->rt_index = pos;
    cl->rt_index = -1;
    
    if (pos > 0 && sched->rt_heap[pos]->cl_d < sched->rt_heap[(pos - 1) / 2]->cl_d)
        heap_sift_up(sched->rt_heap, pos);
    else
        heap_sift_down(sched->rt_heap, sched->rt_heap_size, pos);
}

static void hfsc_update_vt_minmax(hfsc_class_t *parent)
{
    uint64_t vt_min = UINT64_MAX;
    uint64_t vt_max = 0;
    
    for (uint32_t i = 0; i < parent->num_children; i++) {
        hfsc_class_t *child = parent->children[i];
        if (child->state == HFSC_CLASS_ACTIVE) {
            if (child->cl_vt < vt_min) vt_min = child->cl_vt;
            if (child->cl_vt > vt_max) vt_max = child->cl_vt;
        }
    }
    
    parent->cl_cvtmin = vt_min;
    parent->cl_cvtmax = vt_max;
}

static void hfsc_update_cfmin(hfsc_class_t *parent)
{
    uint64_t cf_min = UINT64_MAX;
    
    for (uint32_t i = 0; i < parent->num_children; i++) {
        hfsc_class_t *child = parent->children[i];
        if (child->state == HFSC_CLASS_ACTIVE) {
            if (child->cl_myf < cf_min) cf_min = child->cl_myf;
        }
    }
    
    parent->cl_cfmin = cf_min;
}

/* CRITICAL FIX v1.4: Get maximum VT across all active branches at same level */
static uint64_t hfsc_get_max_vt_at_level(hfsc_class_t *parent)
{
    uint64_t max_vt = 0;
    int count = 0;

    
    if (parent == NULL) return 0;
    
    for (uint32_t i = 0; i < parent->num_children; i++) {
        hfsc_class_t *sibling = parent->children[i];
        if (sibling->state == HFSC_CLASS_ACTIVE) {
            /* Check both the sibling's own VT and its children's VT range */
            // if (sibling->cl_vt > max_vt) {
            //     max_vt = sibling->cl_vt;
            // }
            // if (sibling->cl_cvtmax > max_vt) {
            //     max_vt = sibling->cl_cvtmax;
            // }
            max_vt = max_vt + sibling->cl_vt;
            count++
        }
    }
    
    return max_vt/count;
}

/* CRITICAL FIX v1.4: Proper VT synchronization across branches */
static void hfsc_activate_class(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    uint64_t cur_time = hfsc_get_time();
    
    if (cl->state == HFSC_CLASS_ACTIVE) return;
    
    cl->state = HFSC_CLASS_ACTIVE;
    cl->last_update = cur_time;
    
    if (cl->rsc.m1 > 0 || cl->rsc.m2 > 0) {
        hfsc_update_sc(&cl->cl_rsc, &cl->rsc, cur_time, cl->cumul, sched->tsc_hz);
        hfsc_init_eligible(&cl->cl_eligible, &cl->cl_rsc, &cl->rsc, sched->tsc_hz);
    }
    
    if (cl->fsc.m1 > 0 || cl->fsc.m2 > 0) {
        /* Update FSC based on current service */
        hfsc_update_sc(&cl->cl_fsc, &cl->fsc, cur_time, cl->total, sched->tsc_hz);
        cl->cl_vt = hfsc_sc_y2x(&cl->cl_fsc, cl->total);
        
        if (cl->parent && cl->parent->state == HFSC_CLASS_ACTIVE) {
            /* CRITICAL FIX v1.4: Sync with maximum VT across all active siblings */
            uint64_t max_sibling_vt = hfsc_get_max_vt_at_level(cl->parent);
            
            /* If this class is behind, adjust its VT offset */
            if (cl->cl_parentperiod != cl->parent->cl_vtperiod) {
                cl->cl_parentperiod = cl->parent->cl_vtperiod;
                
                if (max_sibling_vt > cl->cl_vt) {
                    cl->cl_vtoff = max_sibling_vt - cl->cl_vt;
                } else {
                    cl->cl_vtoff = 0;
                }
            }
        } else if (cl->parent) {
            /* Parent is inactive - check if siblings exist at parent level */
            cl->cl_parentperiod = cl->parent->cl_vtperiod;
            
            /* CRITICAL FIX v1.4: Even if parent is inactive, sync with active cousins */
            if (cl->parent->parent) {
                uint64_t max_cousin_vt = hfsc_get_max_vt_at_level(cl->parent->parent);
                if (max_cousin_vt > cl->cl_vt) {
                    cl->cl_vtoff = max_cousin_vt - cl->cl_vt;
                } else {
                    cl->cl_vtoff = 0;
                }
            }
        }
        
        /* Apply offset */
        cl->cl_vt += cl->cl_vtoff;
    }
    
    if (cl->usc.m1 > 0 || cl->usc.m2 > 0) {
        hfsc_update_sc(&cl->cl_usc, &cl->usc, cur_time, cl->total, sched->tsc_hz);
        cl->cl_myf = hfsc_sc_y2x(&cl->cl_usc, cl->total);
    } else {
        cl->cl_myf = UINT64_MAX;
    }
    
    cl->cl_vtperiod++;
    cl->in_vttree = true;
    
    if (cl->parent) {
        hfsc_update_vt_minmax(cl->parent);
        hfsc_update_cfmin(cl->parent);
        
        /* Update parent's own VT based on children */
        if (cl->parent->fsc.m1 > 0 || cl->parent->fsc.m2 > 0) {
            hfsc_update_sc(&cl->parent->cl_fsc, &cl->parent->fsc, cur_time,
                          cl->parent->total, sched->tsc_hz);
            cl->parent->cl_vt = hfsc_sc_y2x(&cl->parent->cl_fsc, cl->parent->total);
            cl->parent->cl_vt += cl->parent->cl_vtoff;
        } else {
            /* Interior node without FSC - use children's VT range */
            if (cl->parent->cl_cvtmin != UINT64_MAX && cl->parent->cl_cvtmax != 0) {
                cl->parent->cl_vt = (cl->parent->cl_cvtmin + cl->parent->cl_cvtmax) / 2;
            }
        }
        
        /* Recursively activate parent */
        hfsc_activate_class(sched, cl->parent);
    }
}

/* CRITICAL FIX v1.3: Reset VT tracking on deactivation */
static void hfsc_deactivate_class(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    if (cl->state != HFSC_CLASS_ACTIVE) return;
    
    if (cl->rt_index >= 0) heap_remove(sched, cl);
    
    cl->state = HFSC_CLASS_INACTIVE;
    cl->in_vttree = false;
    
    if (cl->parent) {
        hfsc_update_vt_minmax(cl->parent);
        hfsc_update_cfmin(cl->parent);
        
        bool has_active_child = false;
        for (uint32_t i = 0; i < cl->parent->num_children; i++) {
            if (cl->parent->children[i]->state == HFSC_CLASS_ACTIVE) {
                has_active_child = true;
                break;
            }
        }
        
        if (!has_active_child) {
            /* Reset VT tracking when last child deactivates */
            cl->parent->cl_cvtmin = UINT64_MAX;
            cl->parent->cl_cvtmax = 0;
            
            hfsc_deactivate_class(sched, cl->parent);
        } else {
            /* CRITICAL FIX v1.4: Update parent VT even if still active */
            if (cl->parent->fsc.m1 == 0 && cl->parent->fsc.m2 == 0) {
                if (cl->parent->cl_cvtmin != UINT64_MAX && cl->parent->cl_cvtmax != 0) {
                    cl->parent->cl_vt = (cl->parent->cl_cvtmin + cl->parent->cl_cvtmax) / 2;
                }
            }
        }
    }
}

static void hfsc_update_ed(hfsc_scheduler_t *sched, hfsc_class_t *cl, uint32_t len)
{
    if (cl->qlen == 0) {
        if (cl->rt_index >= 0) heap_remove(sched, cl);
        return;
    }
    
    if (cl->rsc.m1 == 0 && cl->rsc.m2 == 0) return;
    
    struct rte_mbuf *next;
    if (rte_ring_peek(cl->queue, (void **)&next) == 0) {
        len = rte_pktmbuf_pkt_len(next);
    } else {
        len = 1500;
    }
    
    cl->cl_e = hfsc_sc_y2x(&cl->cl_eligible, cl->cumul);
    cl->cl_d = hfsc_sc_y2x(&cl->cl_rsc, cl->cumul + len);
    
    if (cl->rt_index >= 0) {
        int old_idx = cl->rt_index;
        if (old_idx > 0 && cl->cl_d < sched->rt_heap[(old_idx - 1) / 2]->cl_d) {
            heap_sift_up(sched->rt_heap, old_idx);
        } else {
            heap_sift_down(sched->rt_heap, sched->rt_heap_size, old_idx);
        }
    }
}

/* CRITICAL FIX v1.3: Complete VT propagation */
static void hfsc_update_vt(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    hfsc_class_t *p;
    
    if (cl->fsc.m1 == 0 && cl->fsc.m2 == 0) return;
    
    cl->cl_vt = hfsc_sc_y2x(&cl->cl_fsc, cl->total);
    cl->cl_vt += cl->cl_vtoff;
    
    /* Propagate through ENTIRE hierarchy */
    for (p = cl->parent; p != NULL; p = p->parent) {
        if (p->state != HFSC_CLASS_ACTIVE) break;
        
        hfsc_update_vt_minmax(p);
        
        if (p->fsc.m1 > 0 || p->fsc.m2 > 0) {
            p->cl_vt = hfsc_sc_y2x(&p->cl_fsc, p->total);
            p->cl_vt += p->cl_vtoff;
        } else {
            if (p->cl_cvtmin != UINT64_MAX && p->cl_cvtmax != 0) {
                p->cl_vt = (p->cl_cvtmin + p->cl_cvtmax) / 2;
            }
        }
    }
}

static void hfsc_update_usc(hfsc_scheduler_t *sched, hfsc_class_t *cl)
{
    if (cl->usc.m1 == 0 && cl->usc.m2 == 0) {
        cl->cl_myf = UINT64_MAX;
        return;
    }
    
    cl->cl_myf = hfsc_sc_y2x(&cl->cl_usc, cl->total);
    
    if (cl->parent) {
        hfsc_update_cfmin(cl->parent);
        for (hfsc_class_t *p = cl->parent; p != NULL; p = p->parent) {
            if (p->state != HFSC_CLASS_ACTIVE) break;
            hfsc_update_cfmin(p);
        }
    }
}

static hfsc_class_t *hfsc_select_rt(hfsc_scheduler_t *sched)
{
    hfsc_class_t *cl, *candidates[HFSC_MAX_CLASSES];
    uint32_t num_candidates = 0;
    uint64_t cur_time = hfsc_get_time();
    uint64_t min_deadline = UINT64_MAX;
    
    for (uint32_t i = 0; i < sched->rt_heap_size; i++) {
        cl = sched->rt_heap[i];
        
        if (time_after(cl->cl_e, cur_time)) continue;
        if (time_after(cl->cl_myf, cur_time)) continue;
        
        bool parent_blocked = false;
        for (hfsc_class_t *p = cl->parent; p != NULL; p = p->parent) {
            if (time_after(p->cl_myf, cur_time)) {
                parent_blocked = true;
                break;
            }
        }
        if (parent_blocked) continue;
        
        if (cl->cl_d < min_deadline) min_deadline = cl->cl_d;
    }
    
    if (min_deadline == UINT64_MAX) return NULL;
    
    for (uint32_t i = 0; i < sched->rt_heap_size; i++) {
        cl = sched->rt_heap[i];
        if (cl->cl_d != min_deadline) continue;
        if (time_after(cl->cl_e, cur_time)) continue;
        if (time_after(cl->cl_myf, cur_time)) continue;
        candidates[num_candidates++] = cl;
    }
    
    if (num_candidates == 0) return NULL;
    if (num_candidates == 1) return candidates[0];
    
    static uint32_t rr_counter = 0;
    return candidates[(rr_counter++) % num_candidates];
}

static hfsc_class_t *hfsc_select_ls(hfsc_scheduler_t *sched, hfsc_class_t *p)
{
    hfsc_class_t *cl, *best;
    uint64_t cur_time = hfsc_get_time();
    uint64_t min_vt;
    
    if (p == NULL || p->state != HFSC_CLASS_ACTIVE) return NULL;
    if (time_after(p->cl_myf, cur_time)) return NULL;
    
    if (p->is_leaf) {
        if (p->qlen > 0) return p;
        return NULL;
    }
    
    best = NULL;
    min_vt = UINT64_MAX;
    
    for (uint32_t i = 0; i < p->num_children; i++) {
        cl = p->children[i];
        
        if (cl->state != HFSC_CLASS_ACTIVE) continue;
        if (time_after(cl->cl_myf, cur_time)) continue;
        
        /* CRITICAL FIX v1.7: Refresh child VT before comparing.
         * Without this, VT goes stale and causes unfair selection. */
        if (cl->fsc.m1 > 0 || cl->fsc.m2 > 0) {
            cl->cl_vt = hfsc_sc_y2x(&cl->cl_fsc, cl->total);
            cl->cl_vt += cl->cl_vtoff;
        }
        
        if (cl->cl_vt < min_vt) {
            min_vt = cl->cl_vt;
            best = cl;
        }
    }
    
    if (best == NULL) return NULL;
    return hfsc_select_ls(sched, best);
}

int hfsc_init(hfsc_scheduler_t **sched_out)
{
    hfsc_scheduler_t *sched;
    
    sched = rte_zmalloc("hfsc_sched", sizeof(*sched), RTE_CACHE_LINE_SIZE);
    if (sched == NULL) {
        HFSC_LOG(ERR, "Failed to allocate scheduler\n");
        return -1;
    }
    
    sched->rt_heap_capacity = HFSC_MAX_CLASSES;
    sched->rt_heap = rte_zmalloc("hfsc_heap", 
                                 sizeof(hfsc_class_t *) * sched->rt_heap_capacity,
                                 RTE_CACHE_LINE_SIZE);
    if (sched->rt_heap == NULL) {
        HFSC_LOG(ERR, "Failed to allocate RT heap\n");
        rte_free(sched);
        return -1;
    }
    
    sched->tsc_hz = rte_get_tsc_hz();
    
    HFSC_LOG(INFO, "HFSC scheduler v1.4 initialized (TSC=%lu Hz)\n", sched->tsc_hz);
    
    *sched_out = sched;
    return 0;
}

void hfsc_cleanup(hfsc_scheduler_t *sched)
{
    if (sched == NULL) return;
    
    for (uint32_t i = 0; i < sched->num_classes; i++) {
        hfsc_class_t *cl = sched->classes[i];
        if (cl) {
            if (cl->queue) {
                struct rte_mbuf *m;
                while (rte_ring_dequeue(cl->queue, (void **)&m) == 0) {
                    rte_pktmbuf_free(m);
                }
                rte_ring_free(cl->queue);
            }
            rte_free(cl);
        }
    }
    
    rte_free(sched->rt_heap);
    rte_free(sched);
    
    HFSC_LOG(INFO, "HFSC scheduler cleaned up\n");
}

hfsc_class_t *hfsc_create_root(hfsc_scheduler_t *sched, const hfsc_service_curve_t *rsc,
                               const hfsc_service_curve_t *fsc, const hfsc_service_curve_t *usc)
{
    if (sched->root != NULL) {
        HFSC_LOG(ERR, "Root class already exists\n");
        return NULL;
    }
    
    return hfsc_create_class(sched, NULL, 0, false, rsc, fsc, usc);
}

hfsc_class_t *hfsc_create_class(hfsc_scheduler_t *sched, hfsc_class_t *parent,
                                uint32_t class_id, bool is_leaf,
                                const hfsc_service_curve_t *rsc,
                                const hfsc_service_curve_t *fsc,
                                const hfsc_service_curve_t *usc)
{
    hfsc_class_t *cl;
    char name[64];
    
    if (sched->num_classes >= HFSC_MAX_CLASSES) {
        HFSC_LOG(ERR, "Maximum number of classes reached\n");
        return NULL;
    }
    
    if (fsc == NULL || fsc->m2 == 0) {
        HFSC_LOG(ERR, "FSC is required and m2 must be > 0\n");
        return NULL;
    }
    
    if (usc && usc->m2 < fsc->m2) {
        HFSC_LOG(ERR, "USC m2 must be >= FSC m2\n");
        return NULL;
    }
    
    if (parent && !parent->is_leaf) {
        uint64_t sibling_sum = 0;
        for (uint32_t i = 0; i < parent->num_children; i++) {
            sibling_sum += parent->children[i]->fsc.m2;
        }
        
        if (sibling_sum + fsc->m2 > parent->fsc.m2) {
            HFSC_LOG(ERR, "Class %u exceeds parent capacity\n", class_id);
            return NULL;
        }
    }
    
    cl = rte_zmalloc("hfsc_class", sizeof(*cl), RTE_CACHE_LINE_SIZE);
    if (cl == NULL) {
        HFSC_LOG(ERR, "Failed to allocate class\n");
        return NULL;
    }
    
    cl->class_id = class_id;
    cl->parent = parent;
    cl->is_leaf = is_leaf;
    cl->state = HFSC_CLASS_INACTIVE;
    cl->rt_index = -1;
    
    if (rsc) cl->rsc = *rsc;
    cl->fsc = *fsc;
    if (usc) cl->usc = *usc;
    
    cl->cl_myf = UINT64_MAX;
    cl->cl_cfmin = UINT64_MAX;
    cl->cl_cvtmin = UINT64_MAX;
    
    if (is_leaf) {
        snprintf(name, sizeof(name), "hfsc_q_%u", class_id);
        cl->queue = rte_ring_create(name, HFSC_QUEUE_SIZE, rte_socket_id(),
                                     RING_F_SP_ENQ | RING_F_SC_DEQ);
        if (cl->queue == NULL) {
            HFSC_LOG(ERR, "Failed to create queue for class %u\n", class_id);
            rte_free(cl);
            return NULL;
        }
    }
    
    if (parent) {
        if (parent->num_children >= HFSC_MAX_CHILDREN) {
            HFSC_LOG(ERR, "Parent has too many children\n");
            if (cl->queue) rte_ring_free(cl->queue);
            rte_free(cl);
            return NULL;
        }
        parent->children[parent->num_children++] = cl;
    } else {
        sched->root = cl;
    }
    
    sched->classes[sched->num_classes++] = cl;
    
    HFSC_LOG(INFO, "Created %s class %u (FSC: %lu/%lu/%lu)\n",
             is_leaf ? "leaf" : "interior", class_id, cl->fsc.m1, cl->fsc.d, cl->fsc.m2);
    
    return cl;
}

int hfsc_enqueue(hfsc_scheduler_t *sched, hfsc_class_t *cl, struct rte_mbuf *m)
{
    uint32_t len;
    
    if (!cl->is_leaf) {
        HFSC_LOG(ERR, "Cannot enqueue to non-leaf class\n");
        return -1;
    }
    
    if (rte_ring_full(cl->queue)) {
        cl->stats_drops++;
        sched->total_drops++;
        return -1;
    }
    
    len = rte_pktmbuf_pkt_len(m);
    
    if (cl->state == HFSC_CLASS_INACTIVE) hfsc_activate_class(sched, cl);
    
    if (rte_ring_enqueue(cl->queue, m) < 0) {
        cl->stats_drops++;
        sched->total_drops++;
        return -1;
    }
    
    cl->qlen++;
    cl->qbytes += len;
    sched->total_packets_in++;
    
    if (cl->qlen == 1 && (cl->rsc.m1 > 0 || cl->rsc.m2 > 0)) {
        cl->cl_e = hfsc_sc_y2x(&cl->cl_eligible, cl->cumul);
        cl->cl_d = hfsc_sc_y2x(&cl->cl_rsc, cl->cumul + len);
        heap_insert(sched, cl);
    }
    
    return 0;
}

struct rte_mbuf *hfsc_dequeue(hfsc_scheduler_t *sched)
{
    hfsc_class_t *cl;
    struct rte_mbuf *m;
    uint32_t len;
    uint64_t cur_time;
    bool selected_by_rt = false;
    
    if (sched->root == NULL || sched->root->state != HFSC_CLASS_ACTIVE) return NULL;
    
    cl = hfsc_select_rt(sched);
    if (cl != NULL) {
        selected_by_rt = true;
    } else {
        cl = hfsc_select_ls(sched, sched->root);
    }
    
    if (cl == NULL || !cl->is_leaf) return NULL;
    
    if (rte_ring_dequeue(cl->queue, (void **)&m) < 0) return NULL;
    
    len = rte_pktmbuf_pkt_len(m);
    
    if (unlikely(cl->qlen == 0)) {
        HFSC_LOG(WARNING, "Dequeued from class %u with qlen=0\n", cl->class_id);
        cl->qlen = 1;
    }
    
    cl->qlen--;
    cl->qbytes -= len;
    cl->total += len;
    cl->stats_packets++;
    cl->stats_bytes += len;
    sched->total_packets_out++;
    
    if (selected_by_rt) cl->cumul += len;
    
    cur_time = hfsc_get_time();
    
    if (cl->rsc.m1 > 0 || cl->rsc.m2 > 0) {
        hfsc_update_sc(&cl->cl_rsc, &cl->rsc, cur_time, cl->cumul, sched->tsc_hz);
        hfsc_init_eligible(&cl->cl_eligible, &cl->cl_rsc, &cl->rsc, sched->tsc_hz);
        hfsc_update_ed(sched, cl, len);
    }
    
    if (cl->fsc.m1 > 0 || cl->fsc.m2 > 0) {
        hfsc_update_sc(&cl->cl_fsc, &cl->fsc, cur_time, cl->total, sched->tsc_hz);
        hfsc_update_vt(sched, cl);
    }
    
    if (cl->usc.m1 > 0 || cl->usc.m2 > 0) {
        hfsc_update_sc(&cl->cl_usc, &cl->usc, cur_time, cl->total, sched->tsc_hz);
        hfsc_update_usc(sched, cl);
    }
    
    for (hfsc_class_t *p = cl->parent; p != NULL; p = p->parent) {
        p->total += len;
        if (selected_by_rt) p->cumul += len;
        
        if (p->fsc.m1 > 0 || p->fsc.m2 > 0) {
            hfsc_update_sc(&p->cl_fsc, &p->fsc, cur_time, p->total, sched->tsc_hz);
        }
        if (p->usc.m1 > 0 || p->usc.m2 > 0) {
            hfsc_update_sc(&p->cl_usc, &p->usc, cur_time, p->total, sched->tsc_hz);
            p->cl_myf = hfsc_sc_y2x(&p->cl_usc, p->total);
        }
    }
    
    if (cl->qlen == 0) {
        hfsc_deactivate_class(sched, cl);
        cl->cl_vtperiod++;
    }
    
    return m;
}

bool hfsc_has_packets(hfsc_scheduler_t *sched)
{
    return (sched->root != NULL && sched->root->state == HFSC_CLASS_ACTIVE);
}

void hfsc_get_class_stats(hfsc_class_t *cl, uint64_t *packets, uint64_t *bytes, uint64_t *drops)
{
    if (packets) *packets = cl->stats_packets;
    if (bytes) *bytes = cl->stats_bytes;
    if (drops) *drops = cl->stats_drops;
}

void hfsc_dump_state(hfsc_scheduler_t *sched)
{
    HFSC_LOG(INFO, "=== HFSC State v1.4 ===\n");
    HFSC_LOG(INFO, "Total classes: %u\n", sched->num_classes);
    HFSC_LOG(INFO, "Packets in: %lu, out: %lu, drops: %lu\n",
             sched->total_packets_in, sched->total_packets_out, sched->total_drops);
    
    for (uint32_t i = 0; i < sched->num_classes; i++) {
        hfsc_class_t *cl = sched->classes[i];
        HFSC_LOG(INFO, "  Class %u: %s, qlen=%u, total=%lu, vt=%lu, state=%s\n",
                 cl->class_id, cl->is_leaf ? "LEAF" : "INT",
                 cl->qlen, cl->total, cl->cl_vt,
                 cl->state == HFSC_CLASS_ACTIVE ? "ACTIVE" : "INACTIVE");
    }
}

void hfsc_dump_vt_state(hfsc_scheduler_t *sched)
{
    printf("\n=== Virtual Time State (v1.4) ===\n");
    for (uint32_t i = 0; i < sched->num_classes; i++) {
        hfsc_class_t *cl = sched->classes[i];
        if (cl->state == HFSC_CLASS_ACTIVE) {
            printf("Class %u (%s): vt=%lu, vtoff=%lu, total=%lu, qlen=%u\n",
                   cl->class_id, cl->is_leaf ? "LEAF" : "INT",
                   cl->cl_vt, cl->cl_vtoff, cl->total, cl->qlen);
            if (!cl->is_leaf) {
                printf("  cvtmin=%lu, cvtmax=%lu\n", cl->cl_cvtmin, cl->cl_cvtmax);
            }
        }
    }
    printf("========================\n\n");
}
