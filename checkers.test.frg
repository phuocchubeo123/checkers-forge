#lang forge/froglet

open "checkers.frg"

test suite for topRightValidCapture {
    example BlackPawnTopRightCapture is {one b0: Board, m: Move | topRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackPawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 2
        r_post = `Move0 -> 4
        c_post = `Move0 -> 4

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0
    }

    // Negative test case for White Pawn
    example WhitePawnTopRightCapture is {one b0: Board | {
            no r_pre, c_pre, r_post, c_post: Int | topRightValidCapture[b0, r_pre, c_pre, r_post, c_post, WhitePawn]} 
        } for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 2) -> `WhitePawn0 + 
                        (3, 3) -> `BlackPawn0
    }

    example BlackKingTopRightCapture is {one b0: Board, m: Move | topRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 5
        c_post = `Move0 -> 7

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `BlackKing0 + 
                        (4, 6) -> `WhitePawn0
    }

    // Positive test case for White King
    example WhiteKingTopRightCapture is {one b0: Board, m: Move | topRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhiteKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 5
        c_post = `Move0 -> 7

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `WhiteKing0 + 
                        (4, 6) -> `BlackKing0
    }
}

test suite for topLeftValidCapture {
    example BlackPawnTopLeftCapture is {one b0: Board, m: Move | topLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackPawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 4
        r_post = `Move0 -> 4
        c_post = `Move0 -> 2

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0
    }

    // Negative test case for White Pawn
    example WhitePawnTopLeftCapture is {one b0: Board | {
            no r_pre, c_pre, r_post, c_post: Int | topLeftValidCapture[b0, r_pre, c_pre, r_post, c_post, WhitePawn]} 
        } for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `WhitePawn0 + 
                        (3, 3) -> `BlackPawn0
    }

    example BlackKingTopLeftCapture is {one b0: Board, m: Move | topLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 5
        c_post = `Move0 -> 3

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `BlackKing0 + 
                        (4, 4) -> `WhitePawn0
    }

    // Positive test case for White King
    example WhiteKingTopLeftCapture is {one b0: Board, m: Move | topLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhiteKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 5
        c_post = `Move0 -> 3

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `WhiteKing0 +
                        (4, 4) -> `BlackKing0
    }
}

test suite for bottomRightValidCapture {
    // Negative test case for Black Pawn
    example BlackPawnBottomRightCapture is {one b0: Board | {
            no r_pre, c_pre, r_post, c_post: Int | bottomRightValidCapture[b0, r_pre, c_pre, r_post, c_post, BlackPawn]} 
        } for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (1, 3) -> `WhitePawn0
    }

    // Positive test case for White Pawn
    example WhitePawnBottomRightCapture is {one b0: Board, m: Move | bottomRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhitePawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 2
        r_post = `Move0 -> 0
        c_post = `Move0 -> 4

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 2) -> `WhitePawn0 + 
                        (1, 3) -> `BlackPawn0
    }

    // Positive test case for Black King
    example BlackKingBottomRightCapture is {one b0: Board, m: Move | bottomRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 1
        c_post = `Move0 -> 7

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `BlackKing0 + 
                        (2, 6) -> `WhitePawn0
    }

    // Positive test case for White King
    example WhiteKingBottomRightCapture is {one b0: Board, m: Move | bottomRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhiteKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 1
        c_post = `Move0 -> 7

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `WhiteKing0 +
                        (2, 6) -> `BlackKing0
    }
}

test suite for bottomLeftValidCapture {
    // Negative test case for Black Pawn
    example BlackPawnBottomLeftCapture is {one b0: Board | {
            no r_pre, c_pre, r_post, c_post: Int | bottomLeftValidCapture[b0, r_pre, c_pre, r_post, c_post, BlackPawn]} 
        } for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `BlackPawn0 + 
                        (1, 3) -> `WhitePawn0
    }

    // Positive test case for White Pawn
    example WhitePawnBottomLeftCapture is {one b0: Board, m: Move | bottomLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhitePawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 4
        r_post = `Move0 -> 0
        c_post = `Move0 -> 2

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `WhitePawn0 + 
                        (1, 3) -> `BlackPawn0
    }

    // Positive test case for Black King
    example BlackKingBottomLeftCapture is {one b0: Board, m: Move | bottomLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 1
        c_post = `Move0 -> 3

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `BlackKing0 + 
                        (2, 4) -> `WhitePawn0
    }

    // Positive test case for White King
    example WhiteKingBottomLeftCapture is {one b0: Board, m: Move | bottomLeftValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, WhiteKing]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 3
        c_pre = `Move0 -> 5
        r_post = `Move0 -> 1
        c_post = `Move0 -> 3

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (3, 5) -> `WhiteKing0 +
                        (2, 4) -> `BlackKing0
    }
}

test suite for captureMovesValidity {
    example oneHopBlackPawnCapture is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and captureMovesValidity[b0, b1, BlackPawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (4, 4) -> `BlackPawn0 + 
                        (5, 3) -> `WhitePawn0
        `Board1.board = (6, 2) -> `BlackPawn0
    }

    example twoHopBlackPawnCapture is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and captureMovesValidity[b0, b1, BlackPawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 2 + `Move1 -> 4
        c_pre = `Move0 -> 2 + `Move1 -> 4
        r_post = `Move0 -> 4 + `Move1 -> 6
        c_post = `Move0 -> 4 + `Move1 -> 2

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0 +
                        (5, 3) -> `WhitePawn0
        `Board1.board = (6, 2) -> `BlackPawn0
    }

    example twoHopBlackKingCapture is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and captureMovesValidity[b0, b1, BlackKing] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 2 + `Move1 -> 4
        c_pre = `Move0 -> 2 + `Move1 -> 4
        r_post = `Move0 -> 4 + `Move1 -> 2
        c_post = `Move0 -> 4 + `Move1 -> 6

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (2, 2) -> `BlackKing0 + 
                        (3, 3) -> `WhitePawn0 +
                        (3, 5) -> `WhitePawn0
        `Board1.board = (2, 6) -> `BlackKing0
    }

    example blackPawnCaptureThenPromote is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and captureMovesValidity[b0, b1, BlackPawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 3 + `Move1 -> 5
        c_pre = `Move0 -> 3 + `Move1 -> 5
        r_post = `Move0 -> 5 + `Move1 -> 7
        c_post = `Move0 -> 5 + `Move1 -> 7

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (3, 3) -> `BlackPawn0 + 
                        (4, 4) -> `WhitePawn0 +
                        (6, 6) -> `WhitePawn0 +
                        (1, 3) -> `WhitePawn0
        `Board1.board = (7, 7) -> `BlackKing0 + 
                        (1, 3) -> `WhitePawn0
    }

    example blackPawnCaptureThenNotPromote is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and not captureMovesValidity[b0, b1, BlackPawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 3 + `Move1 -> 5
        c_pre = `Move0 -> 3 + `Move1 -> 5
        r_post = `Move0 -> 5 + `Move1 -> 7
        c_post = `Move0 -> 5 + `Move1 -> 7

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (3, 3) -> `BlackPawn0 + 
                        (4, 4) -> `WhitePawn0 +
                        (6, 6) -> `WhitePawn0
        `Board1.board = (7, 7) -> `BlackPawn0
    }

    example whitePawnCaptureThenPromote is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and captureMovesValidity[b0, b1, WhitePawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 4 + `Move1 -> 2
        c_pre = `Move0 -> 4 + `Move1 -> 2
        r_post = `Move0 -> 2 + `Move1 -> 0
        c_post = `Move0 -> 2 + `Move1 -> 0

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (4, 4) -> `WhitePawn0 + 
                        (3, 3) -> `BlackPawn0 +
                        (1, 1) -> `BlackPawn0
        `Board1.board = (0, 0) -> `WhiteKing0
    }

    example whitePawnCaptureThenNotPromote is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and not captureMovesValidity[b0, b1, WhitePawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 + `Move1
        move_time = `Move0 -> `TIME0 + `Move1 -> `TIME0
        next_move = `Move0 -> `Move1
        r_pre = `Move0 -> 4 + `Move1 -> 2
        c_pre = `Move0 -> 4 + `Move1 -> 2
        r_post = `Move0 -> 2 + `Move1 -> 0
        c_post = `Move0 -> 2 + `Move1 -> 0

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (4, 4) -> `WhitePawn0 + 
                        (3, 3) -> `BlackPawn0 +
                        (1, 1) ->`BlackPawn0
        `Board1.board = (2, 2) ->`WhitePawn0
    }

    example notFullTwoHopBlackPawnCapture is {one b0, b1: Board | b0.board_time.next_time = b1.board_time and not captureMovesValidity[b0, b1, BlackPawn] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 2
        r_post = `Move0 -> 4
        c_post = `Move0 -> 4

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0 +
                        (5, 3) -> `WhitePawn0
        `Board1.board = (6, 2) -> `BlackPawn0
    }
}

test suite for forcedCapture {
    example oneChoiceOfCapture is {one b: Board | forcedCapture[b, BlackPawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0
    }

    example twoChoicesOfCapture is {one b: Board | forcedCapture[b, BlackPawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 4) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0 +
                        (3, 5) -> `WhitePawn0
    }

    example oneBlackTwoWhiteNonCapture is {one b: Board | not forcedCapture[b, BlackPawn]} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0

        Move = `Move0
        move_time = `Move0 -> `TIME0

        Board = `Board0
        board_time = `Board0 -> `TIME0

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 5) -> `WhitePawn0 +
                        (1, 3) -> `WhitePawn0
    }
}

test suite for move {
    example betweenTwoChoices is {one b0, b1: Board | move[b0, b1, 2, 2, 4, 4, Black] and validCaptures} for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 2
        r_post = `Move0 -> 4
        c_post = `Move0 -> 4

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0 +
                        (7, 3) -> `WhitePawn0
        `Board1.board = (4, 4) -> `BlackPawn0 +
                        (7, 3) -> `WhitePawn0
    }

    example betweenTwoChoicesButNotCapture is {one b0, b1: Board | {
                                                not move[b0, b1, 2, 2, 3, 1, Black]
                                                b0.board_time.next_time = b1.board_time
                                                }
        } for {
        PieceRole = `BlackPawn0 + `BlackKing0 + `WhitePawn0 + `WhiteKing0
        BlackPawn = `BlackPawn0
        BlackKing = `BlackKing0
        WhitePawn = `WhitePawn0
        WhiteKing = `WhiteKing0

        Player = `Black0 + `White0
        Black = `Black0
        White = `White0

        TIME = `TIME0 + `TIME1
        next_time = `TIME0 -> `TIME1

        Move = `Move0 
        move_time = `Move0 -> `TIME0
        r_pre = `Move0 -> 2
        c_pre = `Move0 -> 2
        r_post = `Move0 -> 3
        c_post = `Move0 -> 1

        Board = `Board0 + `Board1
        board_time = `Board0 -> `TIME0 + `Board1 -> `TIME1

        `Board0.board = (2, 2) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0
        `Board1.board = (3, 1) -> `BlackPawn0 + 
                        (3, 3) -> `WhitePawn0
    }
}