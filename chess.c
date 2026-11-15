//chess.c   

#include "gameplay.h"
int main() {
    Game g;
    init_game(&g);
    play (&g);
    return 0;
}