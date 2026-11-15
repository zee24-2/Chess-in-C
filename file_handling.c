//file_handling.c

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "gameplay.h"
#include "file_handling.h"

void game_to_fen (const Game *g, char *out){
    int k = 0;
    for (int r = 7; r >= 0; r--){
        int empty = 0;
        for (int c = 0; c < 8; c++){
            char p = g->board[r][c];
            if (p == '.') empty++;
            else{
                if (empty) {
                    out [k++] = '0' + empty;
                    empty = 0;
                }
                out [k++] = p;
            }
        }
        if (empty > 0) {
            out [k++] = '0' + empty;
        }
        if (r > 0){
            out [k++] = '/';
        }
    }

    out [k++] = ' ';
    out [k++] = (g->side == WHITE) ? 'w' : 'b';
    out [k++] = ' ';
    if (g->castle == 0) out [k++] = '-';
    else {
        if (g->castle & 1) out[k++] = 'K';
        if (g->castle & 2) out[k++] = 'Q';
        if (g->castle & 4) out[k++] = 'k';
        if (g->castle & 8) out[k++] = 'q';
    }
    out [k++] = ' ';
    if (g->ep_r < 0) out[k++] = '-';
    else { out[k++] = 'a' + g->ep_c; out[k++] = '1' + g->ep_r; }

    out [k] = '\0';
    char tail[32];
    sprintf(tail, " %d %d", g->halfmove, g->fullmove);
    strcat(out, tail);
}

int fen_to_game (const char *fen, Game *g){
    int r = 7, c = 0;
    int i = 0;

    while (fen[i] != '\0' && fen[i] != ' ') {
        char ch = fen[i++];
        if (ch == '/'){
            r--;
            c = 0;
        }

        else if (ch >= '1' && ch <= '8'){
            int empty = ch - '0';
            for (int j = 0; j < empty; j++){
                if (r < 0 || c > 7) return 0;
                g->board[r][c] = '.';
                c++;
            }
        }

        else{
            if (r < 0 || c > 7) return 0;
            g->board[r][c++] = ch;
        }
    }
    if (r != 0 || c != 8) return 0;

    char side_ch = 0;
    char cast [8] = "-";
    char ep [4] = "-";
    int half = 0;
    int full = 1;

    int n = sscanf (fen + i, " %c %s %s %d %d", &side_ch, cast, ep, &half, &full);
    if (n < 1) return 1;

    if (side_ch == 'w') g->side = WHITE;
    else if (side_ch == 'b') g->side = BLACK;
    else return 0;

    g->castle = 0;
    for (char *q = cast; *q; q++) {
        if (*q == 'K') g->castle += 1;
        if (*q == 'Q') g->castle += 2;
        if (*q == 'k') g->castle += 4;
        if (*q == 'q') g->castle += 8;
    }

    g->ep_r = g->ep_c = -1;
    if (ep[0] >= 'a' && ep[0] <= 'h' && ep[1] >= '1' && ep[1] <= '8') {
        g->ep_c = ep[0] - 'a';
        g->ep_r = ep[1] - '1';
    }
    g->halfmove = half;
    g->fullmove = full;
    return 1;
}

int save_game (const char *filename, const Game *g){
    FILE *f = fopen (filename, "w");
    if (!f) return 0;
    char fen[100];
    game_to_fen (g, fen);
    fprintf(f, "%s\n", fen);
    fclose(f);
    return 1;
}

int open_game(const char *filename, Game *g) {
    FILE *f = fopen(filename, "r");
    if (!f) return 0;

    char board[128], turn, cast[16], ep[16];
    int half, full;
    int n = fscanf(f, "%s %c %s %s %d %d", board, &turn, cast, ep, &half, &full);
    fclose(f);

    if (n != 6) return 0;

    char fen[256];
    sprintf(fen, "%s %c %s %s %d %d", board, turn, cast, ep, half, full);
    return fen_to_game(fen, g);
}

