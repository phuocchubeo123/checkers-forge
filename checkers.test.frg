#lang forge/froglet

open "checkers.frg"

test suite for topRightValidCapture {
    example BlackPawnTopRight is {one b0: Board, m: Move | topRightValidCapture[b0, m.r_pre, m.c_pre, m.r_post, m.c_post, BlackPawn]} for {
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
                        (3, 3) -> `WhitePawn0
        `Board1.board = (4, 4) -> `BlackPawn0
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
        // `Board1.board = (6, 2) -> `BlackPawn0
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
        // `Board1.board = (6, 2) -> `BlackPawn0
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