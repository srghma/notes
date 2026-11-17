```cpp
#include <benchmark/benchmark.h>
#include <vector>
#include <forward_list>
#include <list>
#include <cstddef>

// ======================================================
// Compiler detection (quick-bench lets you pick GCC or
// Clang from the dropdown — this labels each run so you
// can tell which stdlib/compiler produced which numbers)
// ======================================================
#if defined(__clang__)
    #define COMPILER_NAME "Clang"
#elif defined(__GNUC__)
    #define COMPILER_NAME "GCC"
#else
    #define COMPILER_NAME "Unknown"
#endif

// ======================================================
// Struct 1 (Part 1): used by initial-slow and initial-fast
// ======================================================
struct node {
    int value;
    node *next;
};

void remove_list_entry_slow(node **head, node *entry)
{
    node *prev = nullptr, *walk;
    walk = *head;
    while (walk != entry) {
        prev = walk;
        walk = walk->next;
    }
    if (!prev)
        *head = entry->next;
    else
        prev->next = entry->next;
}

void remove_list_entry_fast(node **head, node *entry)
{
    node **p = head;
    while (*p != entry)
        p = &(*p)->next;
    *p = entry->next;
}

// ======================================================
// Struct 2 (Part 2): GLib-style GSList
// ======================================================
struct node_data {
    int value;
};

struct GSList {
    void *data;
    GSList *next;
};

GSList *g_slist_remove_link(GSList *list, GSList *link)
{
    GSList **p;
    for (p = &list; *p; p = &(*p)->next) {
        if (*p != link) continue;
        *p = (*p)->next;
        break;
    }
    return list;
}

// ======================================================
// Struct 3 (Part 3): Linux-style embedded llist_node
// ======================================================
struct llist_node {
    llist_node *next;
};

struct llist_head {
    llist_node *first;
};

struct lnode {
    llist_node node;
    int value;
};

#define llist_for_each(pos, n) for ((pos) = (n); pos; (pos) = (pos)->next)

void llist_del(llist_head *list, llist_node *entry)
{
    llist_node *p;
    llist_for_each(p, (llist_node *)list) {
        if (p->next != entry) continue;
        p->next = entry->next;
        return;
    }
}

// ======================================================
// Benchmarks: build an N-node list, remove the middle
// node, rebuild every iteration (setup excluded via
// PauseTiming/ResumeTiming so we only measure removal).
// ======================================================
static const int N = 1000;

static void BM_InitialSlow(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].next = (i + 1 < N) ? &nodes[i + 1] : nullptr;
        }
        node *head = &nodes[0];
        node *target = &nodes[N / 2];
        state.ResumeTiming();

        remove_list_entry_slow(&head, target);
        benchmark::DoNotOptimize(head);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_InitialSlow);

static void BM_InitialFast(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].next = (i + 1 < N) ? &nodes[i + 1] : nullptr;
        }
        node *head = &nodes[0];
        node *target = &nodes[N / 2];
        state.ResumeTiming();

        remove_list_entry_fast(&head, target);
        benchmark::DoNotOptimize(head);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_InitialFast);

static void BM_GLib(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node_data> data(N);
        std::vector<GSList> links(N);
        for (int i = 0; i < N; i++) {
            data[i].value = i;
            links[i].data = &data[i];
            links[i].next = (i + 1 < N) ? &links[i + 1] : nullptr;
        }
        GSList *list = &links[0];
        GSList *target = &links[N / 2];
        state.ResumeTiming();

        list = g_slist_remove_link(list, target);
        benchmark::DoNotOptimize(list);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_GLib);

static void BM_Linux(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<lnode> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].node.next = (i + 1 < N) ? &nodes[i + 1].node : nullptr;
        }
        llist_head list_head = { &nodes[0].node };
        llist_node *target = &nodes[N / 2].node;
        state.ResumeTiming();

        llist_del(&list_head, target);
        benchmark::DoNotOptimize(list_head.first);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_Linux);

// ======================================================
// std::forward_list (singly linked, C++11 stdlib)
// No O(1) erase-by-iterator exists for forward_list, so
// like the custom singly-linked versions above, we must
// traverse and track the predecessor ourselves.
// ======================================================
static void BM_StdForwardList(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::forward_list<int> flist;
        {
            auto it = flist.before_begin();
            for (int i = 0; i < N; i++)
                it = flist.insert_after(it, i);
        }
        int target_value = N / 2;
        state.ResumeTiming();

        auto prev = flist.before_begin();
        for (auto it = flist.begin(); it != flist.end(); ++it) {
            if (*it == target_value) {
                flist.erase_after(prev);
                break;
            }
            prev = it;
        }
        benchmark::DoNotOptimize(flist);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_StdForwardList);

// ======================================================
// std::list (doubly linked)
// Given an iterator to the target (as if you already held
// a pointer to the node, like the custom versions' `entry`
// argument), erase is O(1) — no predecessor traversal
// needed. This is the whole point of a prev pointer.
// ======================================================
static void BM_StdList(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::list<int> dlist;
        for (int i = 0; i < N; i++)
            dlist.push_back(i);
        auto target_it = dlist.begin();
        std::advance(target_it, N / 2);
        state.ResumeTiming();

        dlist.erase(target_it);
        benchmark::DoNotOptimize(dlist);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_StdList);
```
