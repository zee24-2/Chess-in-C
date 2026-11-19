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

static int static_eval (const Game *g){
    int score = 0;
    for (int r = 7; r >= 0; r--){
        for (int c = 0; c < 8; c++){
            char p = g->board[r][c];
            if (p == '.') continue;
            int v = piece_value (p);
            char np = tolower((unsigned char)p);
            if (np == 'n' || np == 'b' || np == 'p'){
                if ((r<5 && r>2) && (c<5 && c>2)) v+= 50;
            }
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


static int negamax (const Game *g, int depth, int alpha, int beta, int ply){
    int side = (g->side == WHITE) ? 1: -1;
    if (depth ==0){
        return side * static_eval (g);
    }

    int max_eval = -INF;
    MoveList l;
    gen_legal (g, &l);
    order (g, &l);
    if (l.count == 0){
        return in_check (g, g->side) ? -MATE + ply : 0;
    }
    if (g->halfmove >= 100) return 0;

    for (int i = 0; i < l.count; i++){
        Game copy = *g;
        apply_move (&copy, l.move[i]);
        int eval = -negamax (&copy, depth-1, -beta, -alpha, ply+1);
        max_eval = MAX (max_eval, eval);
        alpha = MAX (alpha, eval);
        if (alpha>=beta) break;
    }
    return max_eval;
}


Move best_move(const Game *g, int depth){
    MoveList l;
    gen_legal (g, &l);
    order (g, &l);
    Move best = l.move [0];
    int alpha = -INF;
    int beta = INF;
    for (int i = 0; i<l.count; i++){
        Game copy = *g;
        apply_move (&copy, l.move[i]);
        int eval = -negamax (&copy, depth-1, -beta, -alpha, 1);
        if (eval > alpha){
            alpha = eval;
            best = l.move[i];
        }
    }
    return best;
}