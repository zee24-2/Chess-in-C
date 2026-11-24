//ai.c

#include <ctype.h>
#include "ai.h"

#define INF 100000
#define MATE 50000
#define MAX(a, b) (((a) > (b)) ? (a) : (b))


static int piece_value (char p){
    switch (tolower((unsigned char)p)){
        case 'p': return 100;
        case 'n': return 300;
        case 'b': return 300;
        case 'r': return 500;
        case 'q': return 900;
        default: return 0;
    }
}

// Row 0 = Rank 1 (White home rank), Row 7 = Rank 8 (promotion rank)
static const int PAWN_PST[8][8] = {
    {  0,   0,   0,   0,   0,   0,   0,   0},
    {  5,  10,  10, -20, -20,  10,  10,   5},
    {  5,  -5, -10,   0,   0, -10,  -5,   5},
    {  0,   0,   0,  20,  20,   0,   0,   0},
    {  5,   5,  10,  25,  25,  10,   5,   5},
    { 10,  10,  20,  30,  30,  20,  10,  10},
    { 50,  50,  50,  50,  50,  50,  50,  50},
    {  0,   0,   0,   0,   0,   0,   0,   0}
};

static const int KNIGHT_PST[8][8] = {
    {-50, -40, -30, -30, -30, -30, -40, -50},
    {-40, -20,   0,   5,   5,   0, -20, -40},
    {-30,   5,  10,  15,  15,  10,   5, -30},
    {-30,   0,  15,  20,  20,  15,   0, -30},
    {-30,   5,  15,  20,  20,  15,   5, -30},
    {-30,   0,  10,  15,  15,  10,   0, -30},
    {-40, -20,   0,   0,   0,   0, -20, -40},
    {-50, -40, -30, -30, -30, -30, -40, -50}
};

static const int BISHOP_PST[8][8] = {
    {-20, -10, -10, -10, -10, -10, -10, -20},
    {-10,   5,   0,   0,   0,   0,   5, -10},
    {-10,  10,  10,  10,  10,  10,  10, -10},
    {-10,   0,  10,  10,  10,  10,   0, -10},
    {-10,   5,   5,  10,  10,   5,   5, -10},
    {-10,   0,   5,  10,  10,   5,   0, -10},
    {-10,   0,   0,   0,   0,   0,   0, -10},
    {-20, -10, -10, -10, -10, -10, -10, -20}
};

static const int ROOK_PST[8][8] = {
    {  0,   0,   0,   5,   5,   0,   0,   0},
    { -5,   0,   0,   0,   0,   0,   0,  -5},
    { -5,   0,   0,   0,   0,   0,   0,  -5},
    { -5,   0,   0,   0,   0,   0,   0,  -5},
    { -5,   0,   0,   0,   0,   0,   0,  -5},
    { -5,   0,   0,   0,   0,   0,   0,  -5},
    {  5,  10,  10,  10,  10,  10,  10,   5},
    {  0,   0,   0,   0,   0,   0,   0,   0}
};

static const int QUEEN_PST[8][8] = {
    {-20, -10, -10,  -5,  -5, -10, -10, -20},
    {-10,   0,   5,   0,   0,   0,   0, -10},
    {-10,   5,   5,   5,   5,   5,   0, -10},
    {  0,   0,   5,   5,   5,   5,   0,  -5},
    { -5,   0,   5,   5,   5,   5,   0,  -5},
    {-10,   0,   5,   5,   5,   5,   0, -10},
    {-10,   0,   0,   0,   0,   0,   0, -10},
    {-20, -10, -10,  -5,  -5, -10, -10, -20}
};

static const int KING_MG_PST[8][8] = {
    { 20,  30,  10,   0,   0,  10,  30,  20},
    { 20,  20,   0,   0,   0,   0,  20,  20},
    {-10, -20, -20, -20, -20, -20, -20, -10},
    {-20, -30, -30, -40, -40, -30, -30, -20},
    {-30, -40, -40, -50, -50, -40, -40, -30},
    {-30, -40, -40, -50, -50, -40, -40, -30},
    {-30, -40, -40, -50, -50, -40, -40, -30},
    {-30, -40, -40, -50, -50, -40, -40, -30}
};

static const int KING_EG_PST[8][8] = {
    {-50, -30, -30, -30, -30, -30, -30, -50},
    {-30, -30,   0,   0,   0,   0, -30, -30},
    {-30, -10,  20,  30,  30,  20, -10, -30},
    {-30, -10,  30,  40,  40,  30, -10, -30},
    {-30, -10,  30,  40,  40,  30, -10, -30},
    {-30, -10,  20,  30,  30,  20, -10, -30},
    {-30, -20, -10,   0,   0, -10, -20, -30},
    {-50, -40, -30, -20, -20, -30, -40, -50}
};

static int pst_bonus(char p, int r, int c, int is_endgame) {
    int rr = (colour_of(p) == WHITE) ? r : (7 - r);
    switch (tolower((unsigned char)p)) {
        case 'p': return PAWN_PST[rr][c];
        case 'n': return KNIGHT_PST[rr][c];
        case 'b': return BISHOP_PST[rr][c];
        case 'r': return ROOK_PST[rr][c];
        case 'q': return QUEEN_PST[rr][c];
        case 'k': return is_endgame ? KING_EG_PST[rr][c] : KING_MG_PST[rr][c];
        default:  return 0;
    }
}

static int static_eval(const Game *g) {
    int score = 0;
    int non_pawn_material = 0;

    // First pass: sum material & determine game phase (middlegame vs endgame)
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            char p = g->board[r][c];
            if (p == '.') continue;
            char np = tolower((unsigned char)p);
            if (np != 'p' && np != 'k') {
                non_pawn_material += piece_value(p);
            }
        }
    }
    // Transition king table when total minor/major piece material <= 2600 (e.g., ~1 rook + 1 minor per side)
    int is_endgame = (non_pawn_material <= 2600);

    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            char p = g->board[r][c];
            if (p == '.') continue;
            int v = piece_value(p) + pst_bonus(p, r, c, is_endgame);
            score += (colour_of(p) == WHITE) ? v : -v;
        }
    }
    return score;
}



static int move_value (const Game *g, Move m){
    int value = 0;
    char target = g->board [m.tr][m.tc];
    char attacker = g->board [m.fr][m.fc];
    if (target != '.'){
        value = value + 10*piece_value (target) - piece_value(attacker);
    }
    else if ((tolower ((unsigned char) attacker)) == 'p' && m.fc != m.tc){
        value = value + 10*100 - 100;
    }

    if (m.promo != 0){
        value = value + piece_value (m.promo) - 100;
    }
    return value;
}

static void order (const Game *g, MoveList *l){
    for (int i = 1; i < l->count; i++){
        Move key_move = l->move[i];
        int j = i-1;
        while (j>=0 && move_value (g, l->move[j]) < move_value (g, key_move)){
            l->move[j+1] = l->move[j];
            j--;
        }
        l->move [j+1] = key_move;
    }
}


static int negamax(const Game *g, int depth, int alpha, int beta, int ply) {
    if (ply > 0 && (g->halfmove >= 100 || is_threefold(g) || is_insufficient_material(g))) {
        return 0;
    }

    int side = (g->side == WHITE) ? 1 : -1;
    if (depth == 0) {
        return side * static_eval(g);
    }

    int max_eval = -INF;
    MoveList l;
    gen_legal(g, &l);
    order(g, &l);
    if (l.count == 0) {
        return in_check(g, g->side) ? -MATE + ply : 0;
    }

    for (int i = 0; i < l.count; i++) {
        Game copy = *g;
        apply_move(&copy, l.move[i]);
        int eval = -negamax(&copy, depth - 1, -beta, -alpha, ply + 1);
        max_eval = MAX(max_eval, eval);
        alpha = MAX(alpha, eval);
        if (alpha >= beta) break;
    }
    return max_eval;
}

Move best_move(const Game *g, int depth) {
    MoveList l;
    gen_legal(g, &l);
    if (l.count == 0) {
        Move empty = {0, 0, 0, 0, 0};
        return empty;
    }
    order(g, &l);
    Move best = l.move[0];
    int alpha = -INF;
    int beta = INF;
    for (int i = 0; i < l.count; i++) {
        Game copy = *g;
        apply_move(&copy, l.move[i]);
        int eval = -negamax(&copy, depth - 1, -beta, -alpha, 1);
        if (eval > alpha) {
            alpha = eval;
            best = l.move[i];
        }
    }
    return best;
}