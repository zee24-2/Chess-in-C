#ifndef AI_H
#define AI_H
#include "gameplay.h"

extern long ai_nodes;                       // positions searched in the last search
int  evaluate(const Game *g);
Move best_move(const Game *g, int depth);   // call only if a legal move exists

#endif