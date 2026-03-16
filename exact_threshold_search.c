#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

typedef struct {
    uint64_t a;
    uint64_t b;
} Pair;

typedef struct {
    Pair *keys;
    unsigned char *used;
    uint8_t *depths;
    size_t capacity;
    size_t size;
} DepthTable;

typedef struct {
    int k;
    uint64_t limit;
    int target_depth;
    int bound_mode;
    uint64_t visits;
    uint64_t visit_limit;
    uint64_t progress_interval;
    size_t seen_capacity;
    DepthTable seen;
    Pair witness;
    int found;
} SearchContext;

typedef struct {
    Pair *pairs;
    uint8_t *depths;
    size_t size;
    size_t capacity;
} Frontier;

typedef struct {
    Pair *pairs;
    size_t size;
    size_t capacity;
} PairList;

typedef struct {
    int k;
    uint64_t limit;
    int target_depth;
    int bound_mode;
    uint64_t visits;
    uint64_t visit_limit;
    size_t seen_capacity;
    DepthTable seen;
    PairList pareto;
    int limit_hit;
} CollectContext;

static int generate_predecessors(Pair state, int k, uint64_t limit, Pair *out);

static int bit_length_u64(uint64_t v) {
    if (v == 0) {
        return 0;
    }
    return 64 - __builtin_clzll(v);
}

static uint64_t limit_for_bits(int k) {
    if (k <= 0 || k > 63) {
        return 0;
    }
    return (UINT64_C(1) << k) - 1ULL;
}

static uint64_t gcd_u64(uint64_t a, uint64_t b) {
    if (a == 0) {
        return b;
    }
    if (b == 0) {
        return a;
    }

    {
        int az = __builtin_ctzll(a);
        int bz = __builtin_ctzll(b);
        int shift = (az < bz) ? az : bz;

        a >>= az;
        b >>= bz;

        for (;;) {
            if (a > b) {
                uint64_t tmp = a;
                a = b;
                b = tmp;
            }

            b -= a;
            if (b == 0) {
                return a << shift;
            }
            b >>= __builtin_ctzll(b);
        }
    }
}

static Pair normalize_pair(Pair p) {
    if (p.b == 0) {
        Pair root = {1, 0};
        return root;
    }
    {
        uint64_t g = gcd_u64(p.a, p.b);
        if (g > 1) {
            p.a /= g;
            p.b /= g;
        }
    }
    return p;
}

static size_t hash_u64(uint64_t x);

static int pair_equal(Pair lhs, Pair rhs) {
    return lhs.a == rhs.a && lhs.b == rhs.b;
}

static size_t hash_pair(Pair p) {
    uint64_t mixed = p.a ^ (p.b + 0x9e3779b97f4a7c15ULL +
                            (p.a << 6) + (p.a >> 2));
    return hash_u64(mixed);
}

static int pair_cmp_desc(const void *lhs, const void *rhs) {
    const Pair *a = (const Pair *)lhs;
    const Pair *b = (const Pair *)rhs;
    if (a->a != b->a) {
        return (a->a < b->a) ? 1 : -1;
    }
    if (a->b != b->b) {
        return (a->b < b->b) ? 1 : -1;
    }
    return 0;
}

static int pair_cmp_asc(const void *lhs, const void *rhs) {
    const Pair *a = (const Pair *)lhs;
    const Pair *b = (const Pair *)rhs;
    if (a->a != b->a) {
        return (a->a < b->a) ? -1 : 1;
    }
    if (a->b != b->b) {
        return (a->b < b->b) ? -1 : 1;
    }
    return 0;
}

static void pair_list_init(PairList *list, size_t capacity) {
    list->pairs = malloc(capacity * sizeof(Pair));
    list->size = 0;
    list->capacity = capacity;
    if (list->pairs == NULL) {
        fprintf(stderr, "allocation failed for pair list\n");
        exit(1);
    }
}

static void pair_list_destroy(PairList *list) {
    free(list->pairs);
    list->pairs = NULL;
    list->size = 0;
    list->capacity = 0;
}

static void pair_list_push(PairList *list, Pair pair) {
    if (list->size == list->capacity) {
        list->capacity *= 2;
        list->pairs = realloc(list->pairs, list->capacity * sizeof(Pair));
        if (list->pairs == NULL) {
            fprintf(stderr, "reallocation failed for pair list\n");
            exit(1);
        }
    }
    list->pairs[list->size] = pair;
    list->size += 1;
}

static int pair_dominates(Pair lhs, Pair rhs) {
    return lhs.a <= rhs.a && lhs.b <= rhs.b &&
           (lhs.a < rhs.a || lhs.b < rhs.b);
}

static void pareto_add(PairList *pareto, Pair pair) {
    size_t i;
    size_t out = 0;

    for (i = 0; i < pareto->size; ++i) {
        Pair cur = pareto->pairs[i];
        if (cur.a == pair.a && cur.b == pair.b) {
            return;
        }
        if (pair_dominates(cur, pair)) {
            return;
        }
    }

    for (i = 0; i < pareto->size; ++i) {
        Pair cur = pareto->pairs[i];
        if (pair_dominates(pair, cur)) {
            continue;
        }
        pareto->pairs[out] = cur;
        out += 1;
    }
    pareto->size = out;
    pair_list_push(pareto, pair);
}

static void pareto_merge(PairList *dst, const PairList *src) {
    size_t i;
    for (i = 0; i < src->size; ++i) {
        pareto_add(dst, src->pairs[i]);
    }
}

static size_t hash_u64(uint64_t x) {
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return (size_t)x;
}

static void depth_table_init(DepthTable *table, size_t capacity_pow2) {
    table->capacity = capacity_pow2;
    table->size = 0;
    table->keys = calloc(table->capacity, sizeof(Pair));
    table->used = calloc(table->capacity, sizeof(unsigned char));
    table->depths = calloc(table->capacity, sizeof(uint8_t));
    if (table->keys == NULL || table->used == NULL || table->depths == NULL) {
        fprintf(stderr, "allocation failed for hash table\n");
        exit(1);
    }
}

static void depth_table_destroy(DepthTable *table) {
    free(table->keys);
    free(table->used);
    free(table->depths);
}

static void depth_table_grow(DepthTable *table);

static uint8_t depth_table_get(const DepthTable *table, Pair p) {
    size_t mask = table->capacity - 1;
    size_t idx = hash_pair(p) & mask;
    for (;;) {
        if (!table->used[idx]) {
            return 0;
        }
        if (pair_equal(table->keys[idx], p)) {
            return table->depths[idx];
        }
        idx = (idx + 1) & mask;
    }
}

static void depth_table_set(DepthTable *table, Pair p, uint8_t depth) {
    if ((table->size + 1) * 10 >= table->capacity * 7) {
        depth_table_grow(table);
    }
    size_t mask = table->capacity - 1;
    size_t idx = hash_pair(p) & mask;
    for (;;) {
        if (!table->used[idx]) {
            table->keys[idx] = p;
            table->used[idx] = 1;
            table->depths[idx] = depth;
            table->size += 1;
            return;
        }
        if (pair_equal(table->keys[idx], p)) {
            table->depths[idx] = depth;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

static void depth_table_grow(DepthTable *table) {
    DepthTable grown;
    size_t i;
    depth_table_init(&grown, table->capacity << 1);
    for (i = 0; i < table->capacity; ++i) {
        if (table->used[i]) {
            depth_table_set(&grown, table->keys[i], table->depths[i]);
        }
    }
    free(table->keys);
    free(table->used);
    free(table->depths);
    *table = grown;
}

static void frontier_init(Frontier *frontier, size_t capacity) {
    frontier->pairs = malloc(capacity * sizeof(Pair));
    frontier->depths = malloc(capacity * sizeof(uint8_t));
    frontier->size = 0;
    frontier->capacity = capacity;
    if (frontier->pairs == NULL || frontier->depths == NULL) {
        fprintf(stderr, "allocation failed for frontier\n");
        exit(1);
    }
}

static void frontier_destroy(Frontier *frontier) {
    free(frontier->pairs);
    free(frontier->depths);
}

static void frontier_push(Frontier *frontier, Pair pair, uint8_t depth) {
    if (frontier->size == frontier->capacity) {
        frontier->capacity *= 2;
        frontier->pairs =
            realloc(frontier->pairs, frontier->capacity * sizeof(Pair));
        frontier->depths =
            realloc(frontier->depths, frontier->capacity * sizeof(uint8_t));
        if (frontier->pairs == NULL || frontier->depths == NULL) {
            fprintf(stderr, "reallocation failed for frontier\n");
            exit(1);
        }
    }
    frontier->pairs[frontier->size] = pair;
    frontier->depths[frontier->size] = depth;
    frontier->size += 1;
}

static void build_frontier(int k, int target_depth, Frontier *frontier) {
    uint64_t limit = limit_for_bits(k);
    DepthTable seen;
    Frontier queue;
    size_t head = 0;
    size_t i;
    Pair root = {1, 0};

    depth_table_init(&seen, 1u << 20);
    frontier_init(&queue, 1024);
    frontier_push(&queue, root, 0);
    depth_table_set(&seen, root, 0);

    while (head < queue.size) {
        Pair state = queue.pairs[head];
        uint8_t depth = queue.depths[head];
        Pair preds[256];
        int count;
        int j;
        head += 1;
        if ((int)depth >= target_depth) {
            continue;
        }
        count = generate_predecessors(state, k, limit, preds);
        for (j = 0; j < count; ++j) {
            Pair pred = preds[j];
            uint8_t next_depth = (uint8_t)(depth + 1);
            uint8_t prev = depth_table_get(&seen, pred);
            if (prev >= next_depth) {
                continue;
            }
            depth_table_set(&seen, pred, next_depth);
            frontier_push(&queue, pred, next_depth);
        }
    }

    frontier_init(frontier, 1024);
    for (i = 0; i < queue.size; ++i) {
        if ((int)queue.depths[i] == target_depth &&
            depth_table_get(&seen, queue.pairs[i]) == queue.depths[i]) {
            frontier_push(frontier, queue.pairs[i], queue.depths[i]);
        }
    }

    frontier_destroy(&queue);
    depth_table_destroy(&seen);
}

static int min_drop_for_steps_strong(int steps) {
    static const int remainder_drop[5] = {0, 0, 1, 1, 2};
    return 3 * (steps / 5) + remainder_drop[steps % 5];
}

static int upper_additional_steps(Pair p, int k, int bound_mode) {
    int delta = k - bit_length_u64(p.a);
    int steps = 0;
    if (bound_mode == 0) {
        return 2 * delta + 1;
    }
    while (min_drop_for_steps_strong(steps + 1) <= delta) {
        steps += 1;
    }
    return steps;
}

static void add_candidate(Pair *out, int *count, Pair candidate) {
    int i;
    candidate = normalize_pair(candidate);
    for (i = 0; i < *count; ++i) {
        if (out[i].a == candidate.a && out[i].b == candidate.b) {
            return;
        }
    }
    out[*count] = candidate;
    *count += 1;
}

static int generate_predecessors(Pair state, int k, uint64_t limit, Pair *out) {
    int count = 0;
    uint64_t x = state.a;
    uint64_t y = state.b;

    if (y < x && x != 0) {
        uint64_t b = x;
        uint64_t r = y;
        int bl = bit_length_u64(b);
        int max_e = k - bl;
        int e;
        for (e = 0; e <= max_e; ++e) {
            uint64_t t = b << e;
            if (t <= limit - r) {
                uint64_t a = t + r;
                if (bit_length_u64(a) == bl + e && a >= b) {
                    Pair cand = {a, b};
                    add_candidate(out, &count, cand);
                }
            }
            if (t > r) {
                uint64_t a = t - r;
                if (bit_length_u64(a) == bl + e && a >= b) {
                    Pair cand = {a, b};
                    add_candidate(out, &count, cand);
                }
            }
        }
    }

    if (y != 0) {
        uint64_t b = y;
        uint64_t r = x;
        int bl = bit_length_u64(b);
        int max_e = k - bl;
        int e;
        for (e = 0; e <= max_e; ++e) {
            uint64_t t = b << e;
            if (t <= limit - r) {
                uint64_t a = t + r;
                if (bit_length_u64(a) == bl + e && a >= b) {
                    Pair cand = {a, b};
                    add_candidate(out, &count, cand);
                }
            }
            if (t > r) {
                uint64_t a = t - r;
                if (bit_length_u64(a) == bl + e && a >= b) {
                    Pair cand = {a, b};
                    add_candidate(out, &count, cand);
                }
            }
        }
    }

    qsort(out, (size_t)count, sizeof(Pair), pair_cmp_desc);
    return count;
}

static void search_context_init(SearchContext *ctx,
                                int k,
                                int target_depth,
                                int bound_mode,
                                uint64_t visit_limit,
                                uint64_t progress_interval,
                                size_t seen_capacity) {
    memset(ctx, 0, sizeof(*ctx));
    ctx->k = k;
    ctx->limit = limit_for_bits(k);
    ctx->target_depth = target_depth;
    ctx->bound_mode = bound_mode;
    ctx->visit_limit = visit_limit;
    ctx->progress_interval = progress_interval;
    ctx->seen_capacity = seen_capacity;
    depth_table_init(&ctx->seen, seen_capacity);
}

static void search_context_destroy(SearchContext *ctx) {
    depth_table_destroy(&ctx->seen);
}

static void collect_context_init(CollectContext *ctx,
                                 int k,
                                 int target_depth,
                                 int bound_mode,
                                 uint64_t visit_limit,
                                 size_t seen_capacity) {
    memset(ctx, 0, sizeof(*ctx));
    ctx->k = k;
    ctx->limit = limit_for_bits(k);
    ctx->target_depth = target_depth;
    ctx->bound_mode = bound_mode;
    ctx->visit_limit = visit_limit;
    ctx->seen_capacity = seen_capacity;
    depth_table_init(&ctx->seen, seen_capacity);
    pair_list_init(&ctx->pareto, 16);
}

static void collect_context_destroy(CollectContext *ctx) {
    pair_list_destroy(&ctx->pareto);
    depth_table_destroy(&ctx->seen);
}

static void dfs_threshold(SearchContext *ctx, Pair state, uint8_t depth) {
    Pair preds[256];
    int count;
    int i;

    if (ctx->found) {
        return;
    }

    ctx->visits += 1;
    if (ctx->progress_interval != 0 &&
        (ctx->visits % ctx->progress_interval) == 0) {
        fprintf(stderr,
                "progress visits=%llu states=%zu depth=%u state=%" PRIu64 ",%" PRIu64 "\n",
                (unsigned long long)ctx->visits,
                ctx->seen.size,
                depth,
                state.a,
                state.b);
        fflush(stderr);
    }
    if (ctx->visits > ctx->visit_limit) {
        return;
    }

    if (depth >= (uint8_t)ctx->target_depth) {
        ctx->found = 1;
        ctx->witness = state;
        return;
    }

    if ((int)depth + upper_additional_steps(state, ctx->k, ctx->bound_mode) <
        ctx->target_depth) {
        return;
    }

    count = generate_predecessors(state, ctx->k, ctx->limit, preds);
    for (i = 0; i < count; ++i) {
        Pair pred = preds[i];
        uint8_t prev = depth_table_get(&ctx->seen, pred);
        if (prev != 0 && prev >= (uint8_t)(depth + 1)) {
            continue;
        }
        depth_table_set(&ctx->seen, pred, (uint8_t)(depth + 1));
        dfs_threshold(ctx, pred, (uint8_t)(depth + 1));
        if (ctx->found) {
            return;
        }
    }
}

static void dfs_collect(CollectContext *ctx, Pair state, uint8_t depth) {
    Pair preds[256];
    int count;
    int i;

    if (ctx->limit_hit) {
        return;
    }

    ctx->visits += 1;
    if (ctx->visits > ctx->visit_limit) {
        ctx->limit_hit = 1;
        return;
    }

    if (depth >= (uint8_t)ctx->target_depth) {
        pareto_add(&ctx->pareto, state);
        return;
    }

    if ((int)depth + upper_additional_steps(state, ctx->k, ctx->bound_mode) <
        ctx->target_depth) {
        return;
    }

    count = generate_predecessors(state, ctx->k, ctx->limit, preds);
    for (i = 0; i < count; ++i) {
        Pair pred = preds[i];
        uint8_t prev = depth_table_get(&ctx->seen, pred);
        if (prev != 0 && prev >= (uint8_t)(depth + 1)) {
            continue;
        }
        depth_table_set(&ctx->seen, pred, (uint8_t)(depth + 1));
        dfs_collect(ctx, pred, (uint8_t)(depth + 1));
        if (ctx->limit_hit) {
            return;
        }
    }
}

static void usage(const char *prog) {
    fprintf(stderr,
            "usage: %s search <k> <target-depth> [visit-limit] [progress-interval] "
            "[bound-mode] [start-a start-b start-depth]\n"
            "       %s frontier <k> <depth>\n"
            "       %s parallel <k> <target-depth> <frontier-depth> "
            "[threads] [visit-limit] [bound-mode]\n"
            "       %s max <k> <frontier-depth> [threads] [visit-limit] [bound-mode]\n"
            "       %s table <n> <frontier-depth> [threads] [visit-limit] [bound-mode]\n"
            "       %s pareto <k> <frontier-depth> [threads] [visit-limit] [bound-mode]\n"
            "       %s pareto_table <n> <frontier-depth> [threads] [visit-limit] [bound-mode]\n",
            prog,
            prog,
            prog,
            prog,
            prog,
            prog,
            prog);
    exit(2);
}

static void usage_invalid_k(const char *prog, int k) {
    fprintf(stderr, "invalid k=%d; expected 1 <= k <= 63\n", k);
    usage(prog);
}

static void usage_invalid_n(const char *prog, int n) {
    fprintf(stderr, "invalid n=%d; expected 1 <= n <= 63\n", n);
    usage(prog);
}

static int run_frontier_mode(int argc, char **argv) {
    int k;
    int target_depth;
    size_t i;
    Frontier frontier;

    if (argc != 4) {
        usage(argv[0]);
    }

    k = atoi(argv[2]);
    target_depth = atoi(argv[3]);
    if (k <= 0 || k > 63) {
        usage_invalid_k(argv[0], k);
    }
    if (target_depth < 0) {
        usage(argv[0]);
    }

    build_frontier(k, target_depth, &frontier);
    for (i = 0; i < frontier.size; ++i) {
        printf("%" PRIu64 " %" PRIu64 " %u\n",
               frontier.pairs[i].a,
               frontier.pairs[i].b,
               frontier.depths[i]);
    }

    frontier_destroy(&frontier);
    return 0;
}

static int run_search_mode(int argc, char **argv) {
    SearchContext ctx;
    Pair start = {1, 0};
    uint8_t start_depth = 0;

    if (argc < 4 || argc > 10) {
        usage(argv[0]);
    }

    memset(&ctx, 0, sizeof(ctx));
    ctx.k = atoi(argv[2]);
    ctx.target_depth = atoi(argv[3]);
    ctx.visit_limit = (argc >= 5) ? strtoull(argv[4], NULL, 10) : 100000000ULL;
    ctx.progress_interval =
        (argc >= 6) ? strtoull(argv[5], NULL, 10) : 0ULL;
    ctx.bound_mode = (argc >= 7) ? atoi(argv[6]) : 0;
    if (argc == 10) {
        start.a = strtoull(argv[7], NULL, 10);
        start.b = strtoull(argv[8], NULL, 10);
        start_depth = (uint8_t)strtoul(argv[9], NULL, 10);
        start = normalize_pair(start);
    } else if (argc != 4 && argc != 5 && argc != 6 && argc != 7) {
        usage(argv[0]);
    }

    if (ctx.k <= 0 || ctx.k > 63) {
        fprintf(stderr, "invalid k=%d; expected 1 <= k <= 63\n", ctx.k);
        return 2;
    }
    if (ctx.target_depth < 0) {
        fprintf(stderr, "target depth must be non-negative\n");
        return 2;
    }

    search_context_init(&ctx,
                        ctx.k,
                        ctx.target_depth,
                        ctx.bound_mode,
                        ctx.visit_limit,
                        ctx.progress_interval,
                        1u << 20);
    depth_table_set(&ctx.seen, start, start_depth);

    dfs_threshold(&ctx, start, start_depth);

    printf("k=%d target=%d bound_mode=%d found=%d visits=%llu states=%zu\n",
           ctx.k,
           ctx.target_depth,
           ctx.bound_mode,
           ctx.found,
           (unsigned long long)ctx.visits,
           ctx.seen.size);
    if (ctx.found) {
        printf("witness=%" PRIu64 ",%" PRIu64 "\n",
               ctx.witness.a,
               ctx.witness.b);
    }
    if (ctx.visits > ctx.visit_limit) {
        printf("visit_limit_hit=1\n");
    }

    search_context_destroy(&ctx);
    return 0;
}

typedef struct {
    Frontier *frontier;
    int k;
    int target_depth;
    int bound_mode;
    uint64_t visit_limit;
    atomic_size_t next_index;
    atomic_ullong total_visits;
    atomic_int found;
    atomic_int limit_hit;
    Pair witness;
    pthread_mutex_t witness_mu;
} ParallelControl;

typedef struct {
    Frontier *frontier;
    int k;
    int target_depth;
    int bound_mode;
    uint64_t visit_limit;
    atomic_size_t next_index;
    atomic_ullong total_visits;
    atomic_int limit_hit;
    PairList pareto;
    pthread_mutex_t pareto_mu;
} ParetoControl;

typedef struct {
    int found;
    int limit_hit;
    uint64_t visits;
    size_t frontier_size;
    Pair witness;
} ThresholdResult;

typedef struct {
    int max_steps;
    int limit_hit;
    Pair witness;
} MaxResult;

typedef struct {
    int limit_hit;
    uint64_t visits;
    size_t frontier_size;
    PairList pareto;
} ParetoResult;

typedef struct {
    void *control;
    int worker_id;
} WorkerArgs;

static void *parallel_worker(void *arg) {
    WorkerArgs *args = (WorkerArgs *)arg;
    ParallelControl *control = (ParallelControl *)args->control;

    for (;;) {
        size_t idx;
        SearchContext ctx;
        Pair start;
        uint8_t start_depth;

        if (atomic_load(&control->found)) {
            break;
        }

        idx = atomic_fetch_add(&control->next_index, 1);
        if (idx >= control->frontier->size) {
            break;
        }

        start = control->frontier->pairs[idx];
        start_depth = control->frontier->depths[idx];

        search_context_init(&ctx,
                            control->k,
                            control->target_depth,
                            control->bound_mode,
                            control->visit_limit,
                            0,
                            1u << 16);
        depth_table_set(&ctx.seen, start, start_depth);
        dfs_threshold(&ctx, start, start_depth);
        atomic_fetch_add(&control->total_visits, ctx.visits);
        if (ctx.visits > ctx.visit_limit) {
            atomic_store(&control->limit_hit, 1);
        }
        if (ctx.found) {
            int already_found = atomic_exchange(&control->found, 1);
            if (!already_found) {
                pthread_mutex_lock(&control->witness_mu);
                control->witness = ctx.witness;
                pthread_mutex_unlock(&control->witness_mu);
            }
            search_context_destroy(&ctx);
            break;
        }
        search_context_destroy(&ctx);
    }

    return NULL;
}

static void *pareto_worker(void *arg) {
    WorkerArgs *args = (WorkerArgs *)arg;
    ParetoControl *control = (ParetoControl *)args->control;

    for (;;) {
        size_t idx;
        CollectContext ctx;
        Pair start;
        uint8_t start_depth;

        if (atomic_load(&control->limit_hit)) {
            break;
        }

        idx = atomic_fetch_add(&control->next_index, 1);
        if (idx >= control->frontier->size) {
            break;
        }

        start = control->frontier->pairs[idx];
        start_depth = control->frontier->depths[idx];

        collect_context_init(&ctx,
                             control->k,
                             control->target_depth,
                             control->bound_mode,
                             control->visit_limit,
                             1u << 16);
        depth_table_set(&ctx.seen, start, start_depth);
        dfs_collect(&ctx, start, start_depth);
        atomic_fetch_add(&control->total_visits, ctx.visits);
        if (ctx.limit_hit) {
            atomic_store(&control->limit_hit, 1);
        }
        pthread_mutex_lock(&control->pareto_mu);
        pareto_merge(&control->pareto, &ctx.pareto);
        pthread_mutex_unlock(&control->pareto_mu);
        collect_context_destroy(&ctx);
    }

    return NULL;
}

static int default_thread_count(void) {
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    if (n < 1) {
        return 1;
    }
    if (n > 256) {
        return 256;
    }
    return (int)n;
}

static ThresholdResult parallel_threshold_search(Frontier *frontier,
                                                 int k,
                                                 int target_depth,
                                                 int thread_count,
                                                 uint64_t visit_limit,
                                                 int bound_mode) {
    ParallelControl control;
    pthread_t *threads;
    WorkerArgs *args;
    int i;
    ThresholdResult result;

    memset(&result, 0, sizeof(result));

    memset(&control, 0, sizeof(control));
    control.frontier = frontier;
    control.k = k;
    control.target_depth = target_depth;
    control.bound_mode = bound_mode;
    control.visit_limit = visit_limit;
    atomic_init(&control.next_index, 0);
    atomic_init(&control.total_visits, 0);
    atomic_init(&control.found, 0);
    atomic_init(&control.limit_hit, 0);
    pthread_mutex_init(&control.witness_mu, NULL);

    threads = malloc((size_t)thread_count * sizeof(pthread_t));
    args = malloc((size_t)thread_count * sizeof(WorkerArgs));
    if (threads == NULL || args == NULL) {
        fprintf(stderr, "allocation failed for threads\n");
        exit(1);
    }

    for (i = 0; i < thread_count; ++i) {
        args[i].control = &control;
        args[i].worker_id = i;
        if (pthread_create(&threads[i], NULL, parallel_worker, &args[i]) != 0) {
            fprintf(stderr, "pthread_create failed\n");
            exit(1);
        }
    }

    for (i = 0; i < thread_count; ++i) {
        pthread_join(threads[i], NULL);
    }

    pthread_mutex_destroy(&control.witness_mu);
    free(threads);
    free(args);

    result.found = atomic_load(&control.found);
    result.limit_hit = atomic_load(&control.limit_hit);
    result.visits = atomic_load(&control.total_visits);
    result.frontier_size = frontier->size;
    result.witness = control.witness;
    return result;
}

static ParetoResult parallel_collect_pareto(Frontier *frontier,
                                            int k,
                                            int target_depth,
                                            int thread_count,
                                            uint64_t visit_limit,
                                            int bound_mode) {
    ParetoControl control;
    pthread_t *threads;
    WorkerArgs *args;
    int i;
    ParetoResult result;

    memset(&result, 0, sizeof(result));
    pair_list_init(&result.pareto, 16);

    memset(&control, 0, sizeof(control));
    control.frontier = frontier;
    control.k = k;
    control.target_depth = target_depth;
    control.bound_mode = bound_mode;
    control.visit_limit = visit_limit;
    atomic_init(&control.next_index, 0);
    atomic_init(&control.total_visits, 0);
    atomic_init(&control.limit_hit, 0);
    pair_list_init(&control.pareto, 16);
    pthread_mutex_init(&control.pareto_mu, NULL);

    threads = malloc((size_t)thread_count * sizeof(pthread_t));
    args = malloc((size_t)thread_count * sizeof(WorkerArgs));
    if (threads == NULL || args == NULL) {
        fprintf(stderr, "allocation failed for threads\n");
        exit(1);
    }

    for (i = 0; i < thread_count; ++i) {
        args[i].control = &control;
        args[i].worker_id = i;
        if (pthread_create(&threads[i], NULL, pareto_worker, &args[i]) != 0) {
            fprintf(stderr, "pthread_create failed\n");
            exit(1);
        }
    }

    for (i = 0; i < thread_count; ++i) {
        pthread_join(threads[i], NULL);
    }

    pthread_mutex_destroy(&control.pareto_mu);
    free(threads);
    free(args);

    result.limit_hit = atomic_load(&control.limit_hit);
    result.visits = atomic_load(&control.total_visits);
    result.frontier_size = frontier->size;
    pareto_merge(&result.pareto, &control.pareto);
    qsort(result.pareto.pairs,
          result.pareto.size,
          sizeof(Pair),
          pair_cmp_asc);
    pair_list_destroy(&control.pareto);
    return result;
}

static MaxResult exact_max_for_k(int k,
                                 int frontier_depth,
                                 int thread_count,
                                 uint64_t visit_limit,
                                 int bound_mode,
                                 int lower_bound,
                                 int verbose) {
    Frontier frontier;
    MaxResult out;
    int lo;
    int hi;
    int effective_frontier_depth;

    memset(&out, 0, sizeof(out));
    lo = lower_bound;
    if (lo < 0) {
        lo = 0;
    }
    if (lo > 2 * k - 1) {
        lo = 2 * k - 1;
    }
    hi = 2 * k;

    effective_frontier_depth = frontier_depth;
    if (effective_frontier_depth > lo) {
        effective_frontier_depth = lo;
    }
    if (effective_frontier_depth < 0) {
        effective_frontier_depth = 0;
    }

    build_frontier(k, effective_frontier_depth, &frontier);
    if (verbose) {
        printf("k=%d frontier_depth=%d threads=%d frontier=%zu\n",
               k,
               effective_frontier_depth,
               thread_count,
               frontier.size);
    }

    while (lo + 1 < hi) {
        int mid = lo + (hi - lo) / 2;
        ThresholdResult result = parallel_threshold_search(
            &frontier, k, mid, thread_count, visit_limit, bound_mode);
        if (verbose) {
            printf("check target=%d bound_mode=%d found=%d visits=%llu\n",
                   mid,
                   bound_mode,
                   result.found,
                   (unsigned long long)result.visits);
        }
        if (result.limit_hit) {
            out.limit_hit = 1;
            frontier_destroy(&frontier);
            return out;
        }
        if (result.found) {
            lo = mid;
            out.witness = result.witness;
        } else {
            hi = mid;
        }
    }

    out.max_steps = lo;
    frontier_destroy(&frontier);
    return out;
}

static int run_parallel_mode(int argc, char **argv) {
    int k;
    int target_depth;
    int frontier_depth;
    int thread_count;
    uint64_t visit_limit;
    int bound_mode;
    Frontier frontier;
    ThresholdResult result;

    if (argc < 5 || argc > 8) {
        usage(argv[0]);
    }

    k = atoi(argv[2]);
    target_depth = atoi(argv[3]);
    frontier_depth = atoi(argv[4]);
    thread_count = (argc >= 6) ? atoi(argv[5]) : default_thread_count();
    visit_limit = (argc >= 7) ? strtoull(argv[6], NULL, 10) : 100000000ULL;
    bound_mode = (argc >= 8) ? atoi(argv[7]) : 0;

    if (k <= 0 || k > 63) {
        usage_invalid_k(argv[0], k);
    }
    if (target_depth < 0 || frontier_depth < 0 ||
        frontier_depth > target_depth || thread_count <= 0) {
        usage(argv[0]);
    }

    build_frontier(k, frontier_depth, &frontier);
    result = parallel_threshold_search(
        &frontier, k, target_depth, thread_count, visit_limit, bound_mode);

    printf("k=%d target=%d frontier_depth=%d threads=%d bound_mode=%d found=%d "
           "visits=%llu frontier=%zu\n",
           k,
           target_depth,
           frontier_depth,
           thread_count,
           bound_mode,
           result.found,
           (unsigned long long)result.visits,
           result.frontier_size);
    if (result.found) {
        printf("witness=%" PRIu64 ",%" PRIu64 "\n",
               result.witness.a,
               result.witness.b);
    }
    if (result.limit_hit) {
        printf("visit_limit_hit=1\n");
    }

    frontier_destroy(&frontier);
    return 0;
}

static int run_max_mode(int argc, char **argv) {
    int k;
    int frontier_depth;
    int thread_count;
    uint64_t visit_limit;
    int bound_mode;
    MaxResult result;

    if (argc < 4 || argc > 7) {
        usage(argv[0]);
    }

    k = atoi(argv[2]);
    frontier_depth = atoi(argv[3]);
    thread_count = (argc >= 5) ? atoi(argv[4]) : default_thread_count();
    visit_limit = (argc >= 6) ? strtoull(argv[5], NULL, 10) : 100000000ULL;
    bound_mode = (argc >= 7) ? atoi(argv[6]) : 0;

    if (k <= 0 || k > 63) {
        usage_invalid_k(argv[0], k);
    }
    if (frontier_depth < 0 || thread_count <= 0) {
        usage(argv[0]);
    }

    result = exact_max_for_k(k,
                             frontier_depth,
                             thread_count,
                             visit_limit,
                             bound_mode,
                             0,
                             1);
    if (result.limit_hit) {
        printf("visit_limit_hit=1\n");
        return 1;
    }
    printf("max_steps=%d\n", result.max_steps);
    if (result.witness.a != 0) {
        printf("witness=%" PRIu64 ",%" PRIu64 "\n",
               result.witness.a,
               result.witness.b);
    }
    return 0;
}

static int run_table_mode(int argc, char **argv) {
    int n;
    int frontier_depth;
    int thread_count;
    uint64_t visit_limit;
    int bound_mode;
    int k;
    int lower_bound = 0;

    if (argc < 4 || argc > 7) {
        usage(argv[0]);
    }

    n = atoi(argv[2]);
    frontier_depth = atoi(argv[3]);
    thread_count = (argc >= 5) ? atoi(argv[4]) : default_thread_count();
    visit_limit = (argc >= 6) ? strtoull(argv[5], NULL, 10) : 100000000ULL;
    bound_mode = (argc >= 7) ? atoi(argv[6]) : 0;

    if (n <= 0 || n > 63) {
        usage_invalid_n(argv[0], n);
    }
    if (frontier_depth < 0 || thread_count <= 0) {
        usage(argv[0]);
    }

    for (k = 1; k <= n; ++k) {
        MaxResult result =
            exact_max_for_k(
                k, frontier_depth, thread_count, visit_limit, bound_mode, lower_bound, 0);
        if (result.limit_hit) {
            printf("k=%d visit_limit_hit=1\n", k);
            return 1;
        }
        printf("k=%d max_steps=%d witness=%" PRIu64 ",%" PRIu64 "\n",
               k,
               result.max_steps,
               result.witness.a,
               result.witness.b);
        lower_bound = result.max_steps;
    }

    return 0;
}

static void print_pareto_pairs(const PairList *pareto) {
    size_t i;
    for (i = 0; i < pareto->size; ++i) {
        printf("witness=%" PRIu64 ",%" PRIu64 "\n",
               pareto->pairs[i].a,
               pareto->pairs[i].b);
    }
}

static int run_pareto_mode(int argc, char **argv) {
    int k;
    int frontier_depth;
    int thread_count;
    uint64_t visit_limit;
    int bound_mode;
    int effective_frontier_depth;
    MaxResult max_result;
    Frontier frontier;
    ParetoResult pareto_result;

    if (argc < 4 || argc > 7) {
        usage(argv[0]);
    }

    k = atoi(argv[2]);
    frontier_depth = atoi(argv[3]);
    thread_count = (argc >= 5) ? atoi(argv[4]) : default_thread_count();
    visit_limit = (argc >= 6) ? strtoull(argv[5], NULL, 10) : 100000000ULL;
    bound_mode = (argc >= 7) ? atoi(argv[6]) : 0;

    if (k <= 0 || k > 63) {
        usage_invalid_k(argv[0], k);
    }
    if (frontier_depth < 0 || thread_count <= 0) {
        usage(argv[0]);
    }

    max_result = exact_max_for_k(
        k, frontier_depth, thread_count, visit_limit, bound_mode, 0, 0);
    if (max_result.limit_hit) {
        printf("visit_limit_hit=1\n");
        return 1;
    }

    effective_frontier_depth = frontier_depth;
    if (effective_frontier_depth > max_result.max_steps) {
        effective_frontier_depth = max_result.max_steps;
    }

    build_frontier(k, effective_frontier_depth, &frontier);
    pareto_result = parallel_collect_pareto(
        &frontier, k, max_result.max_steps, thread_count, visit_limit, bound_mode);

    printf("k=%d max_steps=%d frontier_depth=%d threads=%d bound_mode=%d pareto=%zu visits=%llu frontier=%zu\n",
           k,
           max_result.max_steps,
           effective_frontier_depth,
           thread_count,
           bound_mode,
           pareto_result.pareto.size,
           (unsigned long long)pareto_result.visits,
           pareto_result.frontier_size);
    print_pareto_pairs(&pareto_result.pareto);
    if (pareto_result.limit_hit) {
        printf("visit_limit_hit=1\n");
    }

    pair_list_destroy(&pareto_result.pareto);
    frontier_destroy(&frontier);
    return pareto_result.limit_hit ? 1 : 0;
}

static int run_pareto_table_mode(int argc, char **argv) {
    int n;
    int frontier_depth;
    int thread_count;
    uint64_t visit_limit;
    int bound_mode;
    int k;
    int lower_bound = 0;

    if (argc < 4 || argc > 7) {
        usage(argv[0]);
    }

    n = atoi(argv[2]);
    frontier_depth = atoi(argv[3]);
    thread_count = (argc >= 5) ? atoi(argv[4]) : default_thread_count();
    visit_limit = (argc >= 6) ? strtoull(argv[5], NULL, 10) : 100000000ULL;
    bound_mode = (argc >= 7) ? atoi(argv[6]) : 0;

    if (n <= 0 || n > 63) {
        usage_invalid_n(argv[0], n);
    }
    if (frontier_depth < 0 || thread_count <= 0) {
        usage(argv[0]);
    }

    for (k = 1; k <= n; ++k) {
        int effective_frontier_depth;
        MaxResult max_result =
            exact_max_for_k(
                k, frontier_depth, thread_count, visit_limit, bound_mode, lower_bound, 0);
        Frontier frontier;
        ParetoResult pareto_result;
        size_t i;

        if (max_result.limit_hit) {
            printf("k=%d visit_limit_hit=1\n", k);
            return 1;
        }

        effective_frontier_depth = frontier_depth;
        if (effective_frontier_depth > max_result.max_steps) {
            effective_frontier_depth = max_result.max_steps;
        }

        build_frontier(k, effective_frontier_depth, &frontier);
        pareto_result = parallel_collect_pareto(
            &frontier, k, max_result.max_steps, thread_count, visit_limit, bound_mode);

        printf("k=%d max_steps=%d pareto=%zu\n",
               k,
               max_result.max_steps,
               pareto_result.pareto.size);
        for (i = 0; i < pareto_result.pareto.size; ++i) {
            printf("witness=%" PRIu64 ",%" PRIu64 "\n",
                   pareto_result.pareto.pairs[i].a,
                   pareto_result.pareto.pairs[i].b);
        }
        if (pareto_result.limit_hit) {
            printf("k=%d visit_limit_hit=1\n", k);
            pair_list_destroy(&pareto_result.pareto);
            frontier_destroy(&frontier);
            return 1;
        }

        pair_list_destroy(&pareto_result.pareto);
        frontier_destroy(&frontier);
        lower_bound = max_result.max_steps;
    }

    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        usage(argv[0]);
    }
    if (strcmp(argv[1], "frontier") == 0) {
        return run_frontier_mode(argc, argv);
    }
    if (strcmp(argv[1], "search") == 0) {
        return run_search_mode(argc, argv);
    }
    if (strcmp(argv[1], "parallel") == 0) {
        return run_parallel_mode(argc, argv);
    }
    if (strcmp(argv[1], "max") == 0) {
        return run_max_mode(argc, argv);
    }
    if (strcmp(argv[1], "table") == 0) {
        return run_table_mode(argc, argv);
    }
    if (strcmp(argv[1], "pareto") == 0) {
        return run_pareto_mode(argc, argv);
    }
    if (strcmp(argv[1], "pareto_table") == 0) {
        return run_pareto_table_mode(argc, argv);
    }
    usage(argv[0]);
    return 2;
}
