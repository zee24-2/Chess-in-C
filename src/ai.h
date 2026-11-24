//ai.h

#ifndef AI_H
#define AI_H
#include "gameplay.h"

static int  static_eval(const Game *g);
Move best_move(const Game *g, int depth);   // call only if a legal move exists
#endif