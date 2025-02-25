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
    board: pfunc Int -> Int -> PieceRole 
}

pred wellformed {
    all b: Board {
        all row, col: Int | {
            // No piece on squares that have (row+col) being even
            (row < 0 or row > 7 or col < 0 or col > 7 or remainder[subtract[row, col], 2] != 0) 
            implies no b.board[row][col]
        }
    }
}

pred validMoves {
    // Two consecutive moves in a same time should have:
    // The former move's destination = The later move's source
    all m_pre, m_post: Move | m_pre.next_move = m_post implies {
        m_pre.r_post = m_post.r_pre and m_pre.c_post = m_post.c_pre
    }

    // Cannot capture the same piece in a single time
    all m1, m2: Move | {reachable[m2, m1, next_move]} implies {
        // (m1.r_pre + m1.r_post) / 2
        add[m1.r_post, divide[subtract[m1.r_pre, m1.r_post], 2]] != add[m2.r_post, divide[subtract[m2.r_pre, m2.r_post], 2]] and 
        add[m1.c_post, divide[subtract[m1.c_pre, m1.c_post], 2]] != add[m2.c_post, divide[subtract[m2.c_pre, m2.c_post], 2]] // trick to avoid overflow
    }
}

pred validPiece[row, col: Int] {
    (row >= 0 and row < 8 and col >= 0 and col < 8 and remainder[add[row, col], 2] = 0)
}

// These valid capture predicates does not check whether a destination is inbound
// No boolean means not possible to define fun that returns boolean
pred topLeftValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = add[m.r_pre, 2] and m.c_post = subtract[m.c_pre, 2] and
    no b.board[m.r_post][m.c_post] and
    {
        (type = BlackPawn or type = BlackKing) implies {
            b.board[add[m.r_pre, 1]][subtract[m.c_pre, 1]] = WhitePawn or 
            b.board[add[m.r_pre, 1]][subtract[m.c_pre, 1]] = WhiteKing
        }
        (type = WhiteKing) implies {
            b.board[add[m.r_pre, 1]][subtract[m.c_pre, 1]] = BlackPawn or 
            b.board[add[m.r_pre, 1]][subtract[m.c_pre, 1]] = BlackKing
        }
    }
}

pred topRightValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = add[m.r_pre, 2] and m.c_post = add[m.c_pre, 2] and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = BlackPawn or type = BlackKing) implies {
            b.board[add[m.r_pre, 1]][add[m.c_pre, 1]] = WhitePawn or 
            b.board[add[m.r_pre, 1]][add[m.c_pre, 1]] = WhiteKing
        }
        (type = WhiteKing) implies {
            b.board[add[m.r_pre, 1]][add[m.c_pre, 1]] = BlackPawn or 
            b.board[add[m.r_pre, 1]][add[m.c_pre, 1]] = BlackKing
        }
    }
}

pred bottomLeftValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = subtract[m.r_pre, 2] and m.c_post = subtract[m.c_pre, 2] and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = WhitePawn or type = WhiteKing) implies {
            b.board[subtract[m.r_pre, 1]][subtract[m.c_pre, 1]] = BlackPawn or
            b.board[subtract[m.r_pre, 1]][subtract[m.c_pre, 1]] = BlackKing
        }
        (type = BlackKing) implies {
            b.board[subtract[m.r_pre, 1]][subtract[m.c_pre, 1]] = WhitePawn or
            b.board[subtract[m.r_pre, 1]][subtract[m.c_pre, 1]] = WhiteKing
        }
    }
}

pred bottomRightValidCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = subtract[m.r_pre, 2] and m.c_post = add[m.c_pre, 2] and
    no b.board[m.r_post][m.c_post] and 
    {
        (type = WhitePawn or type = WhiteKing) implies {
            b.board[subtract[m.r_pre, 1]][add[m.c_pre, 1]] = BlackPawn or
            b.board[subtract[m.r_pre, 1]][add[m.c_pre, 1]] = BlackKing
        }
        (type = BlackKing) implies {
            b.board[subtract[m.r_pre, 1]][add[m.c_pre, 1]] = WhitePawn or
            b.board[subtract[m.r_pre, 1]][add[m.c_pre, 1]] = WhiteKing
        }
    }
}

pred forcedCapture[b: Board, type: PieceRole] {
    some row, col: Int | {
        b.board[row][col] = type
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
        ((row >= 0) and (row < 3) and (col >= 0) and (col <= 7) and remainder[subtract[row, col], 2] = 0) implies {
            b.board[row][col] = BlackPawn
        }
        ((row <= 7) and (row > 4) and (col >= 0) and (col <= 7) and remainder[subtract[row, col], 2] = 0) implies {
            b.board[row][col] = WhitePawn
        }

        ((row >= 3) and (row <= 4) and (col >= 0) and (col <= 7) and remainder[subtract[row, col], 2] = 0) implies {
            no b.board[row][col]
        }
    }
}

pred topLeftValidNonCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = add[m.r_pre, 1] and m.c_post = subtract[m.c_pre, 1] and no b.board[m.r_post][m.c_post]
    type = BlackPawn or type = BlackKing or type = WhiteKing
}

pred topRightValidNonCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = add[m.r_pre, 1] and m.c_post = add[m.c_pre, 1] and no b.board[m.r_post][m.c_post]
    type = BlackPawn or type = BlackKing or type = WhiteKing
}

pred bottomLeftValidNonCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = subtract[m.r_pre, 1] and m.c_post = subtract[m.c_pre, 1] and no b.board[m.r_post][m.c_post]
    type = WhitePawn or type = WhiteKing or type = BlackKing
}

pred bottomRightValidNonCapture[b: Board, m: Move, type: PieceRole] {
    m.r_post = subtract[m.r_pre, 1] and m.c_post = add[m.c_pre, 1] and no b.board[m.r_post][m.c_post]
    type = WhitePawn or type = WhiteKing or type = BlackKing
}

pred nonCaptureMoveValidity[pre, post: Board, type: PieceRole] {
    one m: Move | {
        m.move_time = pre.board_time
        (
            topLeftValidNonCapture[pre, m, type] or
            topRightValidNonCapture[pre, m, type] or
            bottomLeftValidNonCapture[pre, m, type] or
            bottomRightValidNonCapture[pre, m, type]
        )
        validPiece[m.r_pre, m.c_pre] and validPiece[m.r_post, m.c_post]

        // The original piece to move should be of correct type
        pre.board[m.r_pre][m.c_pre] = type

        // Place the moved piece in the right place
        m.r_post = 7 implies {
            (type = BlackPawn or type = BlackKing) implies {
                post.board[m.r_post][m.c_post] = BlackKing
            }
            (type = WhitePawn or type = WhiteKing) implies {
                post.board[m.r_post][m.c_post] = type
            }
        }

        m.r_post = 0 implies {
            (type = WhitePawn or type = WhiteKing) implies {
                post.board[m.r_post][m.c_post] = WhiteKing
            }
            (type = BlackPawn or type = BlackKing) implies {
                post.board[m.r_post][m.c_post] = type
            }
        }

        (m.r_post != 0 and m.r_post != 7) implies {
            post.board[m.r_post][m.c_post] = type
        }

        // Remove the piece of previous square
        no post.board[m.r_pre][m.c_pre]

        // Now try to place the other pieces in the right place
        all row, col: Int | {(row != m.r_pre or col != m.c_pre) and (row != m.r_post or col != m.c_post)} implies {
            post.board[row][col] = pre.board[row][col]
        }
    }
}

pred captureMovesValidity[pre, post: Board, type: PieceRole] {
    // Define first move and last move in this time
    some firstMove: Move | some LastMove: Move | {
        firstMove.move_time = pre.board_time and LastMove.move_time = pre.board_time
        // Nothing before the first capture
        no m: Move | m.next_move = firstMove
        // No valid capture after the last capture
        no m: Move | {
            (
                topLeftValidCapture[pre, m, type] or
                topRightValidCapture[pre, m, type] or
                bottomLeftValidCapture[pre, m, type] or
                bottomRightValidCapture[pre, m, type]
            )
            validPiece[m.r_pre, m.c_pre] and validPiece[m.r_post, m.c_post]
            m.r_pre = LastMove.r_post and m.c_pre = LastMove.c_post
        }
        // Every move reachable from firstMove should be in the same time
        all m: Move | {reachable[m, firstMove, next_move] or m = firstMove} implies {
            m.move_time = pre.board_time
            (
                topLeftValidCapture[pre, m, type] or
                topRightValidCapture[pre, m, type] or
                bottomLeftValidCapture[pre, m, type] or
                bottomRightValidCapture[pre, m, type]
            )
            validPiece[m.r_pre, m.c_pre] and validPiece[m.r_post, m.c_post]
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
        pre.board[r_pre][c_pre] = BlackPawn or pre.board[r_pre][c_pre] = BlackKing
    }

    p = White implies {
        pre.board[r_pre][c_pre] = WhitePawn or pre.board[r_pre][c_pre] = WhiteKing
    }

    // Test forced capture
    p = Black implies {
        (forcedCapture[pre, BlackPawn] or forcedCapture[pre, BlackKing]) implies {
            captureMovesValidity[pre]
        }

        not captureMovesValidity[pre] implies {
            nonCaptureMoveValidity[pre, post]
        }
    }

    p = White implies {
        (forcedCapture[pre, WhitePawn] or forcedCapture[pre, WhiteKing]) implies captureMovesValidity[pre]

        not captureMovesValidity[pre] implies {
            nonCaptureMoveValidity[pre, post]
        }
    }
}

run {
    wellformed
    one b: Board | {
        initial[b]
    }
} for 1 Board for {next_time is linear}

run {
    wellformed
    one pre, post: Board | {
        initial[pre]
        nonCaptureMoveValidity[pre, post, BlackPawn]
        pre.board_time.next_time = post.board_time
    }
} for 2 Board, 5 Int, 2 TIME for {next_time is linear}

run {
    wellformed
    one b0, b1, b2: Board | {
        initial[b0]
        nonCaptureMoveValidity[b0, b1, BlackPawn]
        nonCaptureMoveValidity[b1, b2, WhitePawn]
        b0.board_time.next_time = b1.board_time
        b1.board_time.next_time = b2.board_time
    }
} for 3 Board, 5 Int, 3 TIME for {next_time is linear}

run {
    wellformed
    one b0, b1, b2, b3: Board | {
        initial[b0]
        nonCaptureMoveValidity[b0, b1, BlackPawn]
        nonCaptureMoveValidity[b1, b2, WhitePawn]
        captureMovesValidity[b2, b3, BlackPawn]
        b0.board_time.next_time = b1.board_time
        b1.board_time.next_time = b2.board_time
        b2.board_time.next_time = b3.board_time
    }
} for 4 Board, 5 Int, 4 TIME for {next_time is linear}