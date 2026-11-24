#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "gameplay.h"
#include "file_handling.h"

static int is_valid_piece(char ch) {
    return strchr("PNBRQKpnbrqk", ch) != NULL;
}

void game_to_fen(const Game *g, char *out) {
    int k = 0;
    for (int r = 7; r >= 0; r--) {
        int empty = 0;
        for (int c = 0; c < 8; c++) {
            char p = g->board[r][c];
            if (p == '.') empty++;
            else {
                if (empty) {
                    out[k++] = (char)('0' + empty);
                    empty = 0;
                }
                out[k++] = p;
            }
        }
        if (empty > 0) {
            out[k++] = (char)('0' + empty);
        }
        if (r > 0) {
            out[k++] = '/';
        }
    }

    out[k++] = ' ';
    out[k++] = (g->side == WHITE) ? 'w' : 'b';
    out[k++] = ' ';
    if (g->castle == 0) out[k++] = '-';
    else {
        if (g->castle & 1) out[k++] = 'K';
        if (g->castle & 2) out[k++] = 'Q';
        if (g->castle & 4) out[k++] = 'k';
        if (g->castle & 8) out[k++] = 'q';
    }
    out[k++] = ' ';
    if (g->ep_r < 0) out[k++] = '-';
    else {
        out[k++] = (char)('a' + g->ep_c);
        out[k++] = (char)('1' + g->ep_r);
    }

    out[k] = '\0';
    char tail[32];
    snprintf(tail, sizeof(tail), " %d %d", g->halfmove, g->fullmove);
    strcat(out, tail);
}

int fen_to_game(const char *fen, Game *g) {
    if (!fen || !g) return 0;

    Game temp;
    memset(&temp, 0, sizeof(Game));

    int r = 7, c = 0;
    int i = 0;
    int w_kings = 0, b_kings = 0;

    // 1. Parse piece placement safely
    while (fen[i] != '\0' && !isspace((unsigned char)fen[i])) {
        char ch = fen[i++];
        if (ch == '/') {
            if (c != 8) return 0; // Rank must have exactly 8 squares before '/'
            r--;
            c = 0;
        } else if (ch >= '1' && ch <= '8') {
            int empty = ch - '0';
            if (r < 0 || c + empty > 8) return 0;
            for (int j = 0; j < empty; j++) {
                temp.board[r][c++] = '.';
            }
        } else if (is_valid_piece(ch)) {
            if (r < 0 || c >= 8) return 0;
            // Pawns cannot exist on the 1st or 8th rank
            if ((ch == 'P' || ch == 'p') && (r == 0 || r == 7)) return 0;
            if (ch == 'K') w_kings++;
            if (ch == 'k') b_kings++;
            temp.board[r][c++] = ch;
        } else {
            return 0; // Unknown/corrupt character
        }
    }

    // Must finish on rank 0, column 8, with exactly 1 King per side
    if (r != 0 || c != 8) return 0;
    if (w_kings != 1 || b_kings != 1) return 0;

    // 2. Parse active side, castling, en passant, and move clocks safely
    char side_str[8] = "";
    char cast[16] = "-";
    char ep[16] = "-";
    int half = 0;
    int full = 1;
    int extra = 0;

    int n = sscanf(fen + i, " %7s %15s %15s %d %d %n", side_str, cast, ep, &half, &full, &extra);
    if (n < 1 || strlen(side_str) != 1) return 0;

    if (side_str[0] == 'w') temp.side = WHITE;
    else if (side_str[0] == 'b') temp.side = BLACK;
    else return 0;

    // Ensure no trailing junk after the 6th field
    if (n == 5) {
        const char *tail = fen + i + extra;
        while (isspace((unsigned char)*tail)) tail++;
        if (*tail != '\0') return 0;
    }

    // Validate castling flags
    temp.castle = 0;
    if (strcmp(cast, "-") != 0) {
        for (size_t q = 0; cast[q] != '\0'; q++) {
            if (cast[q] == 'K' && !(temp.castle & 1)) temp.castle |= 1;
            else if (cast[q] == 'Q' && !(temp.castle & 2)) temp.castle |= 2;
            else if (cast[q] == 'k' && !(temp.castle & 4)) temp.castle |= 4;
            else if (cast[q] == 'q' && !(temp.castle & 8)) temp.castle |= 8;
            else return 0; // Invalid or duplicate castling character
        }
    }
    // Strip impossible castling rights if king/rook aren't on starting squares
    if (temp.board[0][4] != 'K') temp.castle &= ~3;
    if (temp.board[0][7] != 'R') temp.castle &= ~1;
    if (temp.board[0][0] != 'R') temp.castle &= ~2;
    if (temp.board[7][4] != 'k') temp.castle &= ~12;
    if (temp.board[7][7] != 'r') temp.castle &= ~4;
    if (temp.board[7][0] != 'r') temp.castle &= ~8;

    // Validate en passant target square
    temp.ep_r = temp.ep_c = -1;
    if (strcmp(ep, "-") != 0) {
        if (strlen(ep) != 2 || ep[0] < 'a' || ep[0] > 'h') return 0;
        if (temp.side == WHITE && ep[1] != '6') return 0;
        if (temp.side == BLACK && ep[1] != '3') return 0;
        temp.ep_c = ep[0] - 'a';
        temp.ep_r = ep[1] - '1';
    }

    if (half < 0 || full < 1) return 0;
    temp.halfmove = half;
    temp.fullmove = full;

    // 3. Position Legality Check:
    // The side NOT to move cannot currently be in check (otherwise their king could be captured)
    if (in_check(&temp, 1 - temp.side)) return 0;

    // Initialize repetition history with this loaded position
    temp.history_count = 0;
    record_position(&temp);

    *g = temp;
    return 1;
}

int save_game(const char *filename, const Game *g) {
    FILE *f = fopen(filename, "w");
    if (!f) return 0;
    char fen[128];
    game_to_fen(g, fen);
    fprintf(f, "%s\n", fen);
    fclose(f);
    return 1;
}

int open_game(const char *filename, Game *g) {
    FILE *f = fopen(filename, "r");
    if (!f) return 0;

    char fen[256];
    if (!fgets(fen, sizeof(fen), f)) {
        fclose(f);
        return 0;
    }
    fclose(f);

    fen[strcspn(fen, "\r\n")] = '\0';
    return fen_to_game(fen, g);
}