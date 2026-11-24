//file_handling.h

#ifndef FILE_HANDLING_H
#define FILE_HANDLING_H
#include "gameplay.h"

void game_to_fen(const Game *g, char *out);
int fen_to_game(const char *fen, Game *g);
int save_game(const char *filename, const Game *g);
int open_game(const char *filename, Game *g);

#endif