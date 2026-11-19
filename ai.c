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

int static_eval (const Game *g){
    int score = 0;
    for (int r = 7; r >= 0; r--){
        for (int c = 0; c < 8; c++){
            char p = g->board[r][c];
            if (p == '.') continue;
            int v = piece_value (p);
            char np = tolower((unsigned char)p);
            if (np == 'n' || np == 'r' || np == 'b' || np == 'p'){
                if (r<5 && r>2) v+= 25;
                if (c<5 && c>2) v+= 25;
            }
            score += (colour_of(p) == WHITE) ? v : -v;
            
        }
    }
    return score;
}

static int negamax (const Game *g, int depth, int alpha, int beta, int player){
    int side = (player == WHITE) ? 1: -1;
    if (depth ==0){
        return side * static_eval (g);
    }

    int max_eval = -INF;
    MoveList l;
    gen_legal (g, &l);
    if (l.count == 0){
        return in_check (g, g->side) ? -MATE : 0;
    }

    for (int i = 0; i < l.count; i++){
        Game copy = *g;
        apply_move (&copy, l.move[i]);
        int eval = -negamax (&copy, depth-1, -beta, -alpha, 1-player);
        max_eval = MAX (max_eval, eval);
        alpha = MAX (alpha, eval);
        if (alpha>=beta) break;
    }
    return max_eval;
}


Move best_move(const Game *g, int depth){
    MoveList l;
    gen_legal (g, &l);
    Move best = l.move [0];
    int alpha = -INF;
    int beta = INF;
    for (int i = 0; i<l.count; i++){
        Game copy = *g;
        apply_move (&copy, l.move[i]);
        int eval = -negamax (&copy, depth-1, -beta, -alpha, 1-g->side);
        if (eval > alpha){
            alpha = eval;
            best = l.move[i];
        }
    }
    return best;
}