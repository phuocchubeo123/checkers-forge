#lang forge/froglet

-- Only American checkers. No flying king, only move backward.
-- https://en.wikipedia.org/wiki/Checkers

/*
My current model is as follow:
Each move would be assigned a time
In each time, there will be a sequence of moves, which should be assigned the same type (for example, BlackPawn, BlackKing, ...)
There can be no two capture moves in the same time, that have the same middle point (since this piece can only be taken once)
*/

// Pieces
abstract sig PieceRole {}
one sig BlackPawn, BlackKing, WhitePawn, WhiteKing extends PieceRole {}

sig Piece {
    role: lone PieceRole
}

// Players
abstract sig Player {}
one sig Black, White extends Player {}

// Moves
sig TIME {
    next_time: lone TIME
}

// A small move in a sequence of moves in a time
sig Move {
    move_time: one TIME,
    next_move: lone Move,
    r_pre, c_pre, r_post, c_post: one Int
}

// Board
sig Board {
    // Each board will represent a state of the game
    board_time: one TIME,
    board: pfunc Int -> Int -> Piece 
}

pred wellformed[b: Board] {
    all row, col: Int | {
        // No piece on squares that have (row+col) being even
        (row < 0 or row > 7 or col < 0 or col > 7 or remainder[add[row, col], 2] != 0) 
        implies no b.board[row][col]
    }

    // One piece can only be on one square
    all c: Piece | {
        lone row, col: Int | {
            c = b.board[row][col]
        }
    }
}

pred captureMovesValidity[b: Board, type: PieceRole] {
    // Define first move and last move in this time
    some firstMove: Move | some LastMove: Move | {
        firstMove.move_time = b.board_time and LastMove.move_time = b.board_time
        // Nothing before the first capture
        no m: Move | m.next_move = firstMove
        // No valid capture after the last capture
        no m: Move | {
            (
                topLeftValidCapture[b, m, type] or
                topRightValidCapture[b, m, type] or
                bottomLeftValidCapture[b, m, type] or
                bottomRightValidCapture[b, m, type]
            )
            validPiece[m.r_pre, m.c_pre] and validPiece[m.r_post, m.c_post]
            m.r_pre = LastMove.r_post and m.c_pre = LastMove.c_post
        }
        // Every move reachable from firstMove should be in the same time
        all m: Move | {
            reachable[m, firstMove, next_move] implies m.move_time = b.board_time
        }
    }

    // Two consecutive moves in a same time should have:
    // The former move's destination = The later move's source
    all m_pre, m_post: Move | {
        m_pre.next_move = m_post implies {
            m_pre.r_post = m_post.r_pre and m_pre.c_post = m_post.c_pre
        }
    }

    // Cannot capture the same piece in a single time
    no m1, m2: Move | {
        m1 != m2 and
        m1.move_time = m2.move_time and
        // (m1.r_pre + m1.r_post) / 2
        add[m1.r_post, divide[subtract[m1.r_pre, m1.r_post], 2]] = add[m2.r_post, divide[subtract[m2.r_pre, m2.r_post], 2]] and 
        add[m1.c_post, divide[subtract[m1.c_pre, m1.c_post], 2]] = add[m2.c_post, divide[subtract[m2.c_pre, m2.c_post], 2]] // trick to avoid overflow
    }
}

pred nonCaptureMoveValidity[b: Board] {
    one m: Move | {
        m.move_time = b.board_time
        (
            m.r_post = m.r_pre + 1 and m.c_post = m.c_pre + 1 and no b.board[m.r_post][m.c_post] or
            m.r_post = m.r_pre + 1 and m.c_post = m.c_pre - 1 and no b.board[m.r_post][m.c_post] or
            m.r_post = m.r_pre - 1 and m.c_post = m.c_pre + 1 and no b.board[m.r_post][m.c_post] or
            m.r_post = m.r_pre - 1 and m.c_post = m.c_pre - 1 and no b.board[m.r_post][m.c_post]
        )
        validPiece[m.r_pre, m.c_pre] and validPiece[m.r_post, m.c_post]
    }
}

pred validPiece[row, col: Int] {
    (row >= 0 and row < 8 and col >= 0 and col < 8 and remainder[add[row, col], 2] = 0)
}

// These valid capture predicates does not check whether a destination is inbound
// No boolean means not possible to define fun that returns boolean
pred topLeftValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = m.r_pre + 2 and m.c_post = m.c_pre - 2 and
    no b.board[m.r_post][m.c_post] and
    {
        (type = BlackPawn or type = BlackKing) implies {
            some c: Piece | {
                c = b.board[m.r_pre + 1][m.c_pre - 1] and
                c.role = WhitePawn or c.role = WhiteKing
            }
        }
        (type = WhiteKing) implies {
            some c: Piece | {
                c = b.board[m.r_pre + 1][m.c_pre - 1] and
                c.role = BlackPawn or c.role = BlackKing
            }
        }
    }
}

pred topRightValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = m.r_pre + 2 and m.c_post = m.c_pre + 2 and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = BlackPawn or type = BlackKing) implies {
            one c: Piece | {
                c = b.board[m.r_pre + 1][m.c_pre + 1] and
                c.role = WhitePawn or c.role = WhiteKing
            }
        }
        (type = WhiteKing) implies {
            one c: Piece | {
                c = b.board[m.r_pre + 1][m.c_pre + 1] and
                c.role = BlackPawn or c.role = BlackKing
            }
        }
    }
}

pred bottomLeftValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = m.r_pre - 2 and m.c_post = m.c_pre - 2 and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = WhitePawn or type = WhiteKing) implies {
            some c: Piece | {
                c = b.board[m.r_pre - 1][m.c_pre - 1] and
                c.role = BlackPawn or c.role = BlackKing
            }
        }
        (type = BlackKing) implies {
            one c: Piece | {
                c = b.board[m.r_pre - 1][m.c_pre - 1] and
                c.role = WhitePawn or c.role = WhiteKing
            }
        }
    }
}

pred bottomRightValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = m.r_pre - 2 and m.c_post = m.c_pre + 2 and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = WhitePawn or type = WhiteKing) implies {
            one c: Piece | {
                c = b.board[m.r_pre - 1][m.c_pre + 1] and
                c.role = BlackPawn or c.role = BlackKing
            }
        }
        (type = BlackKing) implies {
            one c: Piece | {
                c = b.board[m.r_pre - 1][m.c_pre + 1] and
                c.role = WhitePawn or c.role = WhiteKing
            }
        }
    }
}

pred forcedCapture[b: Board, type: PieceRole] {
    some row, col: Int | {
        one c: Piece | {
            c = b.board[row][col] and
            c.role = type
        }
        some m: Move | {
            m.move_time = b.board_time and
            m.r_pre = row and m.c_pre = col and
            validPiece[m.r_pre, m.c_pre] and
            validPiece[m.r_post, m.c_post] and
            (
                topLeftValidCapture[b, m, type] or 
                topRightValidCapture[b, m, type] or 
                bottomLeftValidCapture[b, m, type] or 
                bottomRightValidCapture[b, m, type]
            )
        }
    }
}

pred initial[b: Board] {
    // Because nothing here is mutable, I cannot initiate takeTopLeft to be none
    // Instead takeTopLeft will be decided later when a move happens

    all row, col: Int | {
        ((row >= 0) and (row < 3) and (col >= 0) and (col <= 7) and remainder[add[row, col], 2] = 0) implies {
            one c: Piece | {
                b.board[row][col] = c and
                c.role = BlackPawn
            }
        }
        (row >= 0 and row > 4 and col >= 0 and col <= 7 and remainder[add[row, col], 2] = 0) implies {
            one c: Piece | {
                b.board[row][col] = c and
                c.role = WhitePawn
            }
        }

        (row >= 3 and row <= 4 and col >= 0 and col <= 7 and remainder[add[row, col], 2] = 0) implies {
            no c: Piece | {
                b.board[row][col] = c
            }
        }
    }
}

// Checkers rules
// Capturing is forced
// Capturing in the whole sequence is forced
// You cannot promote then continue capturing in a same move

pred move[pre, post: Board, r_pre, c_pre, r_post, c_post: Int, p: Player] {
    // GUARD
    p = Black implies {
        one c: Piece | {
            c = pre.board[r_pre][c_pre] and
            c.role = BlackPawn or c.role = BlackKing
        }
    }

    p = White implies {
        one c: Piece | {
            c = pre.board[r_pre][c_pre] and
            c.role = WhitePawn or c.role = WhiteKing
        }
    }

    // Test forced capture
    p = Black implies {
        (forcedCapture[pre, BlackPawn] or forcedCapture[pre, BlackKing]) implies captureMovesValidity[pre]

    }
}

run {
    one b: Board | {
        initial[b]
        wellformed[b]
    }
} for 1 Board, 24 Piece for {next_time is linear}

