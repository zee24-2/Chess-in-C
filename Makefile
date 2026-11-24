CC = gcc
CFLAGS = -Wall -Wextra -std=c99 -O2

ENGINE_SRC = src/gameplay.c src/file_handling.c src/ai.c
MAIN_SRC   = src/chess.c $(ENGINE_SRC)
TEST_SRC   = tests/perft.c $(ENGINE_SRC)

all: chess

chess: $(MAIN_SRC)
	$(CC) $(CFLAGS) $(MAIN_SRC) -o chess

test: $(TEST_SRC)
	$(CC) $(CFLAGS) $(TEST_SRC) -o perft_test
	./perft_test

clean:
	rm -f chess perft_test *.o dafny/*.cs dafny/*.dll dafny/*.exe dafny/*.json
	rm -rf dafny/bin dafny/obj

.PHONY: all test clean