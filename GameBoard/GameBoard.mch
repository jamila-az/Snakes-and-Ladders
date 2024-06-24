/* My Snakes and Ladders Game :D
 * Author: jamila
 * Creation date: 12/06/2024
 */



MACHINE
    GameBoard

SETS
    // All the possible game statuses
    STATUS = {NewGameStarted, DescendedSnake, AscendedLadder, OverRoll, Victory, NormalMove}

CONSTANTS
    BOARD, SNAKE_POSITIONS, LADDER_POSITIONS, START_SQUARE, LAST_SQUARE, DICE_VALUES

PROPERTIES
    // Define the board, snakes, ladders, and dice values
    BOARD = 1..100 &
    SNAKE_POSITIONS = {31 |-> 4, 16 |-> 13, 47 |-> 25, 63 |-> 60, 66 |-> 52, 97 |-> 75} &
    LADDER_POSITIONS = {3 |-> 39, 10 |-> 12, 27 |-> 53, 56 |-> 84, 72 |-> 90, 61 |-> 99} &
    START_SQUARE = 0 &
    LAST_SQUARE = 100 &
    // Ensure snake heads are above their tails and within proper bounds
    !head.(head : dom(SNAKE_POSITIONS) => (head > SNAKE_POSITIONS(head) & head > 10 & head < 100)) &
    // Ensure ladder bottoms are below their tops and within proper bounds
    !bottom.(bottom : dom(LADDER_POSITIONS) => (bottom < LADDER_POSITIONS(bottom) & bottom < 91)) &
    // Snakes and ladders don't overlap
    (ran(SNAKE_POSITIONS) /\ ran(LADDER_POSITIONS) = {}) &
    (dom(SNAKE_POSITIONS) /\ dom(LADDER_POSITIONS) = {}) &
    // Define dice values
    DICE_VALUES <: NAT1 & DICE_VALUES = 1..6

VARIABLES
    current_dice, previous_dice, player_position, turn_count, snake_count, ladder_count, path_traversed

INVARIANT
    // Invariant properties of the game state
    current_dice : DICE_VALUES &
    previous_dice : DICE_VALUES \/ {0} &
    player_position : BOARD &
    turn_count : NAT &
    snake_count : NAT &
    ladder_count : NAT &
    path_traversed : seq(BOARD)

INITIALISATION
    // Initial game state setup
    current_dice, previous_dice, player_position, turn_count, snake_count, ladder_count, path_traversed :=
    1, 0, START_SQUARE, 0, 0, 0, []

OPERATIONS

    // Roll the dice and move the player
    game_status, new_square <-- RollDice(rolled_value) = 
    PRE
        // Ensure the dice value is valid and the player hasn't already won
        rolled_value : DICE_VALUES & player_position /= LAST_SQUARE
    THEN
        // Update the previous dice value
        previous_dice := rolled_value ||
        // Increment the turn count
        turn_count := succ(turn_count) ||
        // Check if the new position is within the board
        IF (player_position + rolled_value) <= LAST_SQUARE THEN
            // Check if the player wins
            IF (player_position + rolled_value) = LAST_SQUARE THEN
                game_status := Victory ||
                new_square := (player_position + rolled_value) ||
                player_position := (player_position + rolled_value) ||
                path_traversed := path_traversed <- (player_position + rolled_value)
            ELSE
                // Check if the new position is neither a snake nor a ladder
                IF (player_position + rolled_value) /: dom(SNAKE_POSITIONS) & (player_position + rolled_value) /: dom(LADDER_POSITIONS) THEN
                    game_status := NormalMove ||
                    path_traversed := path_traversed <- (player_position + rolled_value) ||
                    player_position := (player_position + rolled_value) ||
                    new_square := (player_position + rolled_value) 
                ELSE
                    // Check if the new position is a snake head
                    IF (player_position + rolled_value) : dom(SNAKE_POSITIONS) THEN   
                        game_status := DescendedSnake ||                               
                        path_traversed := path_traversed ^  [(player_position + rolled_value), SNAKE_POSITIONS(player_position + rolled_value)] || 
                        snake_count := succ(snake_count) ||
                        player_position := SNAKE_POSITIONS(player_position + rolled_value) ||
                        new_square := SNAKE_POSITIONS(player_position + rolled_value) 
                    ELSE 
                        // The new position must be a ladder bottom
                        game_status := AscendedLadder ||
                        path_traversed := path_traversed ^  [(player_position + rolled_value), LADDER_POSITIONS(player_position + rolled_value)] ||
                        ladder_count := succ(ladder_count) ||
                        player_position := LADDER_POSITIONS(player_position + rolled_value) ||
                        new_square := LADDER_POSITIONS(player_position + rolled_value)                     
                    END              
                END
            END
        ELSE
            // If the roll is too high to finish
            game_status := OverRoll ||
            new_square := player_position
        END
    END;

    // Display game statistics
    pos, snakes, ladders, turns <-- Statistics =
    BEGIN
        pos, snakes, ladders, turns := player_position, snake_count, ladder_count, turn_count
    END;

    // Display the path traversed
    traversed_squares <-- Path =
    BEGIN
        traversed_squares := path_traversed
    END;

    // Reset the game to start anew
    game_status <-- ResetGame =
    BEGIN
        current_dice, previous_dice, player_position, turn_count, snake_count, ladder_count, path_traversed :=
        1, 0, START_SQUARE, 0, 0, 0, [START_SQUARE] ||
        game_status := NewGameStarted
    END
END
