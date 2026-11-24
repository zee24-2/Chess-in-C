#include <stdio.h>
#include <stdlib.h>
#include "../src/gameplay.h"
#include "../src/file_handling.h"

static unsigned long long perft(const Game *g, int depth) {
    if (depth == 0) return 1ULL;

    MoveList l;
    gen_legal(g, &l);
    if (depth == 1) return (unsigned long long)l.count;

    unsigned long long nodes = 0;
    for (int i = 0; i < l.count; i++) {
        Game copy = *g;
        apply_move(&copy, l.move[i]);
        nodes += perft(&copy, depth - 1);
    }
    return nodes;
}

static int run_case(const char *name, const char *fen, int depth, unsigned long long expected) {
    Game g;
    init_game(&g);
    if (!fen_to_game(fen, &g)) {
        printf("[FAIL] %s: invalid FEN\n", name);
        return 0;
    }
    unsigned long long got = perft(&g, depth);
    if (got == expected) {
        printf("[ OK ] %-10s depth %d: %llu\n", name, depth, got);
        return 1;
    } else {
        printf("[FAIL] %-10s depth %d: got %llu, expected %llu\n", name, depth, got, expected);
        return 0;
    }
}

int main(void) {
    int passed = 1;
    passed &= run_case("start",     "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 3, 8902);
    passed &= run_case("kiwipete",  "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 3, 97862);
    passed &= run_case("position3", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 3, 2812);
    passed &= run_case("position4", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 3, 9467);
    passed &= run_case("position5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 3, 62379);

    return passed ? 0 : 1;
}