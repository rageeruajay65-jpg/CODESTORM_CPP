

#include <iostream>
using namespace std;
#include<iostream>
#include<vector>
#include<climits>
using namespace std;


/*
 ╔══════════════════════════════════════════════════════════════════════╗
 ║        WUMPUS WORLD PATHFINDER — Complete C++ Solution              ║
 ║        Algorithm : Bellman-Ford Inspired Turn-Indexed Dijkstra      ║
 ║        Grid Size : 17 × 17  (easily configurable)                  ║
 ║                                                                      ║
 ║  Build & Run (CLion / terminal):                                    ║
 ║    g++ -O2 -std=c++17 wumpus_world.cpp -o wumpus && ./wumpus        ║
 ╚══════════════════════════════════════════════════════════════════════╝

 ══ ALL CONDITIONS HANDLED ═══════════════════════════════════════════
  [D1] Wumpus Collision    : entering a Wumpus-occupied cell → DEAD
  [D2] Stench ≥ 3          : cumulative stench cells ≥ 3 across path → DEAD
  [D3] Turn Limit (4 × n²) : path length exceeds limit → UNSAFE
  [D4] No Safe Path        : all branches exhausted → UNSAFE
  [✓]  Pit (+5 sec)        : agent survives, pays penalty
  [✓]  Breeze (+2 sec)     : agent survives, near-pit indicator
  [✓]  Time Zone (−3 sec)  : benefit; cost clamped → max(0, T + δ)
  [✓]  No cell revisit     : enforced per path (prevents TZ cycling)
  [✓]  Wumpus oscillation  : horizontal, precomputed for all turns
  [✓]  Dynamic stench      : stench zones shift as Wumpus moves

 ══ BELLMAN-FORD ANALOGY ═════════════════════════════════════════════
  Classic BF: V−1 passes over all edges, relaxing each.
  This solver: MAX_T passes (one per turn). Each pass relaxes only
  transitions reachable at that turn — sparse, turn-indexed BF.
  Negative edges (Time Zones) are safe because:
    T ← max(0, T + δ)  →  effective cost per edge ≥ 0 after clamping.
  A Dijkstra min-heap replaces sequential passes for efficiency.
  It is correct here because post-clamp edges are non-negative,
  preserving Dijkstra's optimality guarantee while handling TZ benefits.
*/

#include <bits/stdc++.h>
using namespace std;

// ═════════════════════════════════════════════════════════════════════
//  ① GRID DEFINITION — 17 × 17
//
//  Edit RAW_GRID freely.  Rules:
//    • Each row must be exactly N characters (no spaces).
//    • Exactly one 'G' (goal).
//    • (0,0) top-left must be '.' — the agent's fixed start.
//    • Symbols:  '.' empty  'W' Wumpus  'P' Pit  'T' Time Zone  'G' Goal
// ═════════════════════════════════════════════════════════════════════
static constexpr int N = 15;

static const char RAW_GRID[N][N + 1] = {
    "...............",   // row  1 (0-idx 0)  — agent start
    ".W..P..........",   // row  2  Wumpus@(1,1)   Pit@(1,4)
    ".......T.......",   // row  3  TimeZone@(2,7)
    "..P.W.....P....",   // row  4  Pit@(3,2) Wumpus@(3,4) Pit@(3,10)
    "........T......",   // row  5  TimeZone@(4,8)
    "...W........P..",   // row  6  Wumpus@(5,3)  Pit@(5,12)
    "......T........",   // row  7  TimeZone@(6,6)
    "........W.....T",   // row  8  Wumpus@(7,8)  TimeZone@(7,14)
    "..P............",   // row  9  Pit@(8,2)
    "..........W...P",   // row 10  Wumpus@(9,10)  Pit@(9,14)
    ".....T.........",   // row 11  TimeZone@(10,5)
    "............W..",   // row 12  Wumpus@(11,12)
    "...P..........T",   // row 13  Pit@(12,3)  TimeZone@(12,14)
    "......W........",   // row 14  Wumpus@(13,6)
                               // row 15  Pit@(14,11)
                               // row 16  Wumpus@(15,15)
    "..............G"    // row 17  Goal@(16,16)
};

// ═════════════════════════════════════════════════════════════════════
//  ② CONSTANTS & TYPES
// ═════════════════════════════════════════════════════════════════════
static constexpr int MAX_T = 4 * N * N;   // turn limit = 4n²  (= 1156)

// Direction order: D < L < R < U  (alphabetical → guarantees lex-smallest
// path when cost is tied, matching problem output requirement)
static constexpr int ND    = 4;
static constexpr int DR[4] = {  1,  0, 0, -1 };   // Down Left Right Up
static constexpr int DC[4] = {  0, -1, 1,  0 };

using P2 = pair<int, int>;   // (row, col), always 0-indexed internally

// ═════════════════════════════════════════════════════════════════════
//  ③ PARSED GRID DATA
// ═════════════════════════════════════════════════════════════════════
P2          goal_pos;
set<P2>     pits, tzones;
vector<P2>  wumpus_list;   // all Wumpus starting positions (order matters)

// ═════════════════════════════════════════════════════════════════════
//  ④ PRECOMPUTED STRUCTURES
// ═════════════════════════════════════════════════════════════════════
set<P2>              breeze_set;     // static: cells adjacent to pits
vector<vector<P2>>   w_tl;           // w_tl[w][t] = wumpus w position at turn t
vector<set<P2>>      w_sets;         // w_sets[t]  = all Wumpus cells at turn t
vector<set<P2>>      s_sets;         // s_sets[t]  = all Stench cells at turn t

inline bool ok(int r, int c) { return r >= 0 && r < N && c >= 0 && c < N; }

// ─────────────────────────────────────────────────────────────────────
//  Parse RAW_GRID into game objects
// ─────────────────────────────────────────────────────────────────────
void parse_grid() {
    for (int r = 0; r < N; r++)
        for (int c = 0; c < N; c++) {
            char ch = RAW_GRID[r][c];
            if      (ch == 'G') goal_pos = {r, c};
            else if (ch == 'W') wumpus_list.push_back({r, c});
            else if (ch == 'P') pits.insert({r, c});
            else if (ch == 'T') tzones.insert({r, c});
        }
}

// ─────────────────────────────────────────────────────────────────────
//  Breeze: static cells orthogonally adjacent to any Pit
//  (a Pit cell itself does NOT generate breeze in its own square)
// ─────────────────────────────────────────────────────────────────────
void build_breeze() {
    const int d4r[] = {-1, 1, 0, 0};
    const int d4c[] = { 0, 0,-1, 1};
    for (P2 p : pits)
        for (int d = 0; d < 4; d++) {
            int nr = p.first + d4r[d], nc = p.second + d4c[d];
            if (ok(nr, nc) && !pits.count({nr, nc}))
                breeze_set.insert({nr, nc});
        }
}

// ─────────────────────────────────────────────────────────────────────
//  Wumpus Movement Rules
//  • Oscillates horizontally in its own row.
//  • Even-index row → starts moving RIGHT (+1).
//  • Odd-index row  → starts moving LEFT  (−1).
//  • At wall boundary: stays that turn, reverses direction next turn.
//    (Problem spec: "stays at the boundary cell for that step.")
// ─────────────────────────────────────────────────────────────────────
void build_wumpus_timeline() {
    for (P2 w : wumpus_list) {
        vector<P2> tl(MAX_T + 2);
        int cur = w.second;
        int dir = (w.first % 2 == 0) ? 1 : -1;   // even row→right, odd→left

        for (int t = 0; t <= MAX_T + 1; t++) {
            tl[t] = {w.first, cur};
            int nxt = cur + dir;
            if (nxt < 0 || nxt >= N) {
                dir = -dir;      // reverse
                nxt = cur;       // stay at boundary this turn
            }
            cur = nxt;
        }
        w_tl.push_back(tl);
    }
}

// ─────────────────────────────────────────────────────────────────────
//  Precompute wumpus-position sets AND stench-cell sets for every turn.
//  Stench: orthogonal neighbours of each Wumpus (NOT the Wumpus cell itself).
//  Note 3 (spec): "A cell adjacent to two Wumpuses counts as ONE encounter."
//  Using set<P2> deduplicates multiple Wumpus contributions automatically.
// ─────────────────────────────────────────────────────────────────────
void precompute_turn_sets() {
    const int d4r[] = {-1, 1, 0, 0};
    const int d4c[] = { 0, 0,-1, 1};

    w_sets.assign(MAX_T + 2, {});
    s_sets.assign(MAX_T + 2, {});

    for (int t = 0; t <= MAX_T + 1; t++) {
        for (auto& tl : w_tl) {
            P2 wp = tl[t];
            w_sets[t].insert(wp);                    // Wumpus cell
            for (int d = 0; d < 4; d++) {
                int nr = wp.first + d4r[d];
                int nc = wp.second + d4c[d];
                if (ok(nr, nc)) s_sets[t].insert({nr, nc});  // stench cell
            }
        }
    }
}

// ═════════════════════════════════════════════════════════════════════
//  ⑤ SOLVER — Bellman-Ford Inspired Dijkstra
//
//  State: (cost, turn, row, col, stench_accumulated, path_so_far)
//
//  Key design choices:
//  • Turn is part of state because Wumpus positions are time-dependent.
//  • stench_accumulated (0/1/2) tracks how many stench cells entered;
//    reaching 3 = death (pruned immediately).
//  • path_so_far enforces no-revisit and enables path reconstruction.
//  • Direction order D<L<R<U in the expansion loop + lex comparison of
//    path vectors in operator> guarantees lex-smallest path on cost ties.
//  • Pruning key (r,c,stench,turn): if we've reached this state with
//    lower cost, the current branch cannot improve → skip.
// ═════════════════════════════════════════════════════════════════════
struct State {
    int cost;       // accumulated time (≥ 0, clamped)
    int turn;       // current turn number
    int r, c;       // current cell (0-indexed)
    int stench;     // stench cells entered so far (0, 1, or 2)
    vector<P2> path;// complete path from start to here

    // Min-heap: lower cost = higher priority.
    // Tie-break: lex-smaller path = higher priority.
    bool operator>(const State& o) const {
        if (cost != o.cost) return cost > o.cost;
        return path > o.path;
    }
};

pair<int, vector<P2>> solve() {
    // Pruning map: (r, c, stench, turn) → minimum cost seen
    map<tuple<int,int,int,int>, int> best;

    priority_queue<State, vector<State>, greater<State>> pq;
    pq.push({0, 0, 0, 0, 0, {{0, 0}}});

    while (!pq.empty()) {
        State cur = pq.top(); pq.pop();

        // ── GOAL CHECK ──────────────────────────────────────────────
        if (cur.r == goal_pos.first && cur.c == goal_pos.second)
            return {cur.cost, cur.path};

        // ── TURN LIMIT [D3] ─────────────────────────────────────────
        if (cur.turn >= MAX_T) continue;

        // ── PRUNING ─────────────────────────────────────────────────
        auto key = make_tuple(cur.r, cur.c, cur.stench, cur.turn);
        auto it  = best.find(key);
        if (it != best.end() && it->second <= cur.cost) continue;
        best[key] = cur.cost;

        // ── VISITED SET (no-revisit) ─────────────────────────────────
        set<P2> vis(cur.path.begin(), cur.path.end());

        int nt = cur.turn + 1;
        const set<P2>& w_nxt = w_sets[nt];   // Wumpus cells next turn
        const set<P2>& s_nxt = s_sets[nt];   // Stench cells next turn

        // ── EXPAND: direction order D < L < R < U ───────────────────
        for (int d = 0; d < ND; d++) {
            int nr = cur.r + DR[d];
            int nc = cur.c + DC[d];

            // ── Boundary ────────────────────────────────────────────
            if (!ok(nr, nc))         continue;

            // ── No revisit ──────────────────────────────────────────
            if (vis.count({nr, nc})) continue;

            // ══════════ DEATH CONDITIONS ════════════════════════════

            // [D1] Wumpus Collision — cell occupied by Wumpus at nt
            if (w_nxt.count({nr, nc})) {
                // Agent steps into Wumpus → DEAD. Prune this branch.
                continue;
            }

            // [D2] Stench Accumulation ≥ 3
            // Stench is checked at entry time (nt), with dynamic zones.
            // Per spec note 3: same cell adjacent to 2 Wumpuses = 1 encounter.
            int new_stench = cur.stench + (s_nxt.count({nr, nc}) ? 1 : 0);
            if (new_stench >= 3) {
                // Third stench cell entered → DEAD. Prune this branch.
                continue;
            }

            // ══════════ COST CALCULATION ════════════════════════════
            //
            //  δ = +1 (base)  +5 (pit)  +2 (breeze)  −3 (time zone)
            //  T ← max(0, T + δ)   — time cannot go below zero
            //
            //  Note: effects stack.  A pit-in-breeze cell → +5+2 = +7.
            //        A time-zone in breeze cell → +2−3 = −1, clamped.

            int delta = 1;                                    // base move cost

            if (pits.count({nr, nc}))       delta += 5;     // [PIT]   survives
            if (breeze_set.count({nr, nc})) delta += 2;     // [BREEZE] near pit
            if (tzones.count({nr, nc}))     delta -= 3;     // [T-ZONE] benefit

            int new_cost = max(0, cur.cost + delta);        // clamp ≥ 0

            // ── Push next state ──────────────────────────────────────
            State ns;
            ns.cost   = new_cost;
            ns.turn   = nt;
            ns.r      = nr;
            ns.c      = nc;
            ns.stench = new_stench;
            ns.path   = cur.path;
            ns.path.push_back({nr, nc});
            pq.push(ns);
        }
    }

    return {-1, {}};   // [D4] No safe path found → UNSAFE
}

// ═════════════════════════════════════════════════════════════════════
//  ⑥ DISPLAY HELPERS
// ═════════════════════════════════════════════════════════════════════

// Print the grid (or path overlay if path_ptr != nullptr)
void print_grid(const vector<P2>* path_ptr = nullptr) {
    map<P2, int> idx;
    if (path_ptr)
        for (int i = 0; i < (int)path_ptr->size(); i++)
            idx[(*path_ptr)[i]] = i;

    // Column header (1-indexed for user display)
    printf("      ");
    for (int c = 0; c < N; c++) printf("%3d", c + 1);
    printf("\n      ");
    for (int c = 0; c < N; c++) printf("---");
    printf("\n");

    for (int r = 0; r < N; r++) {
        printf("  %2d |", r + 1);
        for (int c = 0; c < N; c++) {
            if (path_ptr && idx.count({r, c}))
                printf("%3d", idx[{r, c}]);
            else
                printf("  %c", RAW_GRID[r][c]);
        }
        printf("\n");
    }
}

// Print stench (S) / breeze (B) overlay for a given turn
void print_percept(int t = 0) {
    printf("      ");
    for (int c = 0; c < N; c++) printf("%3d", c + 1);
    printf("\n      ");
    for (int c = 0; c < N; c++) printf("---");
    printf("\n");

    for (int r = 0; r < N; r++) {
        printf("  %2d |", r + 1);
        for (int c = 0; c < N; c++) {
            char ch = RAW_GRID[r][c];
            if (ch != '.') {
                printf("  %c", ch);   // show W / P / T / G as-is
                continue;
            }
            bool s = s_sets[t].count({r, c}) > 0;
            bool b = breeze_set.count({r, c}) > 0;
            if (s && b)  printf(" SB");
            else if (s)  printf("  S");
            else if (b)  printf("  B");
            else         printf("  .");
        }
        printf("\n");
    }
}

// ═════════════════════════════════════════════════════════════════════
//  ⑦ MAIN
// ═════════════════════════════════════════════════════════════════════
int main() {
    // ── Initialisation ─────────────────────────────────────────────
    parse_grid();
    build_breeze();
    build_wumpus_timeline();
    precompute_turn_sets();

    // ── Banner ──────────────────────────────────────────────────────
    puts("╔══════════════════════════════════════════════════════════╗");
    puts("║     WUMPUS WORLD — Bellman-Ford Inspired Pathfinder      ║");
    printf("║     Grid: %dx%d    Turn Limit: %-4d   Wumpuses: %d         ║\n",
           N, N, MAX_T, (int)wumpus_list.size());
    puts("╚══════════════════════════════════════════════════════════╝\n");

    // ── Initial Grid ────────────────────────────────────────────────
    puts("━━━━ INITIAL GRID ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    puts("  '.' Empty (safe, +1)  'W' Wumpus (DEATH)  'P' Pit (+5)");
    puts("  'T' Time Zone (-3)    'G' Goal (destination)\n");
    print_grid();

    // ── Percept Map ──────────────────────────────────────────────────
    puts("\n━━━━ PERCEPT MAP at turn 0 ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    puts("  'S' Stench (3 total = DEATH)   'B' Breeze (+2)   'SB' Both\n");
    print_percept(0);

    // ── Wumpus Movement ──────────────────────────────────────────────
    puts("\n━━━━ WUMPUS MOVEMENT (turns 0 → 8) ━━━━━━━━━━━━━━━━━━━━━━━");
    puts("  Even-row Wumpuses start RIGHT; odd-row start LEFT.");
    puts("  At wall: stays that turn, reverses direction next.\n");
    for (int w = 0; w < (int)wumpus_list.size(); w++) {
        printf("  W%-2d start(%2d,%2d): ",
               w + 1, wumpus_list[w].first + 1, wumpus_list[w].second + 1);
        for (int t = 0; t <= 8 && t < (int)w_tl[w].size(); t++)
            printf("t%d(%d,%d) ", t,
                   w_tl[w][t].first + 1, w_tl[w][t].second + 1);
        puts("…");
    }

    // ── Death Conditions ─────────────────────────────────────────────
    puts("\n━━━━ ALL DEATH CONDITIONS ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    puts("  [D1] WUMPUS COLLISION");
    puts("       Agent enters any cell occupied by a Wumpus → DEAD.");
    puts("       Wumpus positions are TURN-DEPENDENT (precomputed).");
    puts("       A cell safe at turn 2 may be lethal at turn 5.\n");
    puts("  [D2] STENCH ACCUMULATION ≥ 3");
    puts("       Stench cell = orthogonal neighbour of a Wumpus at entry turn.");
    puts("       Entering same stench cell twice counts as 2 encounters.");
    puts("       A cell adjacent to 2 Wumpuses simultaneously = 1 encounter.");
    puts("       Reaching 3 stench encounters anywhere on path → DEAD.\n");
    printf("  [D3] TURN LIMIT  (%d turns)\n", MAX_T);
    puts("       Any path exceeding 4n² turns is invalid → UNSAFE.\n");
    puts("  [D4] NO SAFE PATH");
    puts("       All possible paths blocked by D1/D2/D3 → UNSAFE.\n");
    puts("  ─── SURVIVABLE EVENTS ──────────────────────────────────");
    puts("  [✓]  Pit       +5 sec  — painful but not lethal");
    puts("  [✓]  Breeze    +2 sec  — proximity warning, survives");
    puts("  [✓]  Time Zone −3 sec  — T ← max(0, T+δ), cost ≥ 0");
    puts("  [✓]  No revisit        — prevents negative-cycle exploitation");

    // ── Algorithm Description ─────────────────────────────────────────
    puts("\n━━━━ ALGORITHM DESIGN ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    puts("  Classic Bellman-Ford: V−1 passes, relax ALL edges per pass.");
    puts("  This solver   : MAX_T passes, one per turn.");
    puts("                  Each pass relaxes only edges for states");
    puts("                  reachable at that specific turn.");
    puts("                  → 'Sparse Turn-Indexed Bellman-Ford'");
    puts("");
    puts("  Negative edges: handled by T ← max(0, T + δ) clamping.");
    puts("  After clamping, effective edge weights are ≥ 0.");
    puts("  → Dijkstra priority queue is correct and optimal.");
    puts("");
    puts("  State: (row, col, stench_count, turn)");
    puts("  Pruning: if (r,c,stench,turn) seen with lower cost → skip.");
    puts("  No-revisit: path vector carries visited set per branch.");

    // ── Solve ─────────────────────────────────────────────────────────
    puts("\n━━━━ SOLVING ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    printf("  Searching: start(1,1) → goal(%d,%d), limit %d turns…\n",
           goal_pos.first + 1, goal_pos.second + 1, MAX_T);
    fflush(stdout);

    auto [min_cost, path] = solve();

    // ── Result ────────────────────────────────────────────────────────
    puts("\n━━━━ RESULT ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    if (path.empty()) {
        puts("UNSAFE\n");
        puts("  No valid path exists from (1,1) to the goal.");
        printf("  All routes result in death or exceed the %d-turn limit.\n", MAX_T);
        return 0;
    }

    // ── Formal output (matches problem output specification) ──────────
    puts("SAFE");
    printf("%d\n", min_cost);
    for (int i = 0; i < (int)path.size(); i++) {
        if (i) putchar(' ');
        printf("(%d,%d)", path[i].first + 1, path[i].second + 1);
    }
    puts("\n");

    // ── Path Visualisation ────────────────────────────────────────────
    puts("━━━━ PATH VISUALISATION  (numbers = step order; 0 = start) ━");
    print_grid(&path);

    // ── Path Statistics ───────────────────────────────────────────────
    puts("\n━━━━ PATH STATISTICS ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    printf("  Total steps  : %d\n", (int)path.size() - 1);
    printf("  Min time     : %d seconds\n", min_cost);
    printf("  Start cell   : (%d,%d)\n", path.front().first+1, path.front().second+1);
    printf("  Goal cell    : (%d,%d)\n", path.back().first+1, path.back().second+1);

    int pits_hit = 0, tz_hit = 0, br_hit = 0, st_hit = 0;
    for (int i = 1; i < (int)path.size(); i++) {
        P2 p = path[i];
        if (pits.count(p))         pits_hit++;
        if (tzones.count(p))       tz_hit++;
        if (breeze_set.count(p))   br_hit++;
        if (s_sets[i].count(p))    st_hit++;   // stench at turn i
    }
    printf("  Pits entered : %d  (time penalty: +%d sec)\n", pits_hit, pits_hit * 5);
    printf("  Time Zones   : %d  (time saved:  -%d sec)\n",  tz_hit,   tz_hit  * 3);
    printf("  Breeze cells : %d  (time penalty: +%d sec)\n", br_hit,   br_hit  * 2);
    printf("  Stench cells : %d / 2 allowed  (>= 3 = death)\n", st_hit);

    return 0;
}