#ifndef FUNCTIONS_H
#define FUNCTIONS_H

/******************************** Struct Definitions ********************************/
// SYNTAX
// Struct definition of a token lexeme pair
struct token_lexeme{
	char *my_token;                  // The token of a token-lexeme pair
    int my_token_num;                // The numeric representation of a token in a token-lexeme pair
	char *my_lexeme;                 // The lexeme of a token-lexeme pair
    int my_lexeme_num;               // The numeric representaition of a lexeme in a token-lexeme pair
	int is_int_flag;                 // Flag to distinguish between int and double. True(1) if value is Number integer, False(0) otherwise.
};

// Struct definition of an AST node
struct node{
    int value;                       // Value of node
    int size;                        // Stores size of my productions
    int terminal_flag;               // True(1) if node represents a terminal, False(0) if node represents a production rule
    char* lexeme;                    // Holds lexeme for terminal nodes. Used for generating TAC
    int index;                       // Stores index of next node to traverse
    struct node* parent;             // Pointer to parent node for traversal
    struct node** children;          // Array of productions from node
    int type;
};


// SEMANTIC
// Variable struct, basically a tuple holds lexeme, var type
struct variable{
    int  line;                      // Stores line number for symbol table
    char *lexeme;                   // Stores variable name
    int variable_type;              // Stores variable type (1 for int || 0 for double)

};

// Track scopes
struct scope{
    int line;                       // Line number, for print to file
    struct scope *parent_scope;     // Pointer to parent for checking broader scopes when variable is not found
    int num_vars;                   // Number of variables, used for memory allocation
    struct variable* local_vars;    // Holds variables for this scope
};

// Holds function information
struct function{
    int line;                       //
    char *lexeme;                   //
    int return_type;                //
    int num_params;                 //
    int *param_types;               //
    struct scope *my_scope;         //
};

// Global scope, holds scope and ponters to all defined functions
struct global{
    struct function *functions;     //
    int num_functions;              //
    struct scope my_scope;          //
};

// A struct for type checking variables for function calls. Important for when function calls are passed as parameters in other functions.
struct check_functions{
    struct function** functions;    //
    int* indeces;                   //
    int num_functions;              //
};

/******************************** Helper Functions ********************************/
// HEADER REPLACEMENTS
// strComp but not from a library
int compare_strings(const char* str1, const char* str2) {
    while (*str1 && *str2 && *str1 == *str2) {
        str1++;
        str2++;
    }
    return *(unsigned char*)str1 - *(unsigned char*)str2;
}

// Binary search but not from a library
int binary_search(const char *arr[], const char* target, int size) {
    int left = 0;
    int right = size-1;

    while (left <= right) {
        int mid = left + (right - left) / 2;

        int cmp = compare_strings(arr[mid], target);

        if (cmp == 0) {
            return mid;
        } else if (cmp < 0) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    return -1;  // String not found
}

// Returns a copy of a char pointer
char* copy_string(const char* src) {
    if (src == NULL) {
        return NULL;
    }
    
    // Calculate the length of the source string
    int length = 0;
    while (src[length] != '\0') {
        length++;
    }
    
    // Allocate memory for the new string (including space for null terminator)
    char* dest = malloc(length + 1);
    if (dest == NULL) {
        return NULL; // Memory allocation failed
    }
    
    // Copy characters from source to destination
    for (int i = 0; i <= length; i++) {
        dest[i] = src[i];
    }
    
    return dest;
}

// LEXICAL
// For number tokens with integer values
void appendInteger(char* lexeme, int* lexeme_index) {
	lexeme[(*lexeme_index)++] = ' ';
    lexeme[(*lexeme_index)++] = ',';
    lexeme[(*lexeme_index)++] = ' ';
    lexeme[(*lexeme_index)++] = 'i';
    lexeme[(*lexeme_index)++] = 'n';
    lexeme[(*lexeme_index)++] = 't';
    lexeme[(*lexeme_index)++] = 'e';
    lexeme[(*lexeme_index)++] = 'g';
    lexeme[(*lexeme_index)++] = 'e';
    lexeme[(*lexeme_index)++] = 'r';
}

// For number tokens with double values
void appendDouble(char* lexeme, int* lexeme_index) {
	lexeme[(*lexeme_index)++] = ' ';
    lexeme[(*lexeme_index)++] = ',';
    lexeme[(*lexeme_index)++] = ' ';
    lexeme[(*lexeme_index)++] = 'd';
    lexeme[(*lexeme_index)++] = 'o';
    lexeme[(*lexeme_index)++] = 'u';
    lexeme[(*lexeme_index)++] = 'b';
    lexeme[(*lexeme_index)++] = 'l';
    lexeme[(*lexeme_index)++] = 'e';
}

// SYNTAX
// Reset token lexeme values
void clear_tl(struct token_lexeme *tl){
    tl->my_token = "";
    tl->my_token_num = -1;
    tl->my_lexeme = "";
    tl->my_lexeme_num = -1;
    tl->is_int_flag = -1;
}

// Sets numeric representations of tl struct given tl with token and lexeme identified 
void set_tl_nums(struct token_lexeme *tl){
    const char* empty = "";
    // Error handling for t-l pair with undefined token or lex
    if(tl == NULL || compare_strings(tl->my_token, empty) == 0 || compare_strings(tl->my_lexeme, empty) == 0){
        printf("Error: Invalid tl used in set_tl_nums\n");
        return;
    }

    // Definitions for use in the compare strings function
    const char *integer = "int";
    const char *doub = "double";

    // Binary search on table tokens in ll1.h to get a numeric value of tls token
    tl->my_token_num = binary_search(tokens, tl->my_token, 10) + 1;

    // Checks if token is one of a type that has different terminals based on it's lexeme
    if(tl->my_token_num == 4 || tl->my_token_num == 5 || tl->my_token_num == 10){
        if(tl->my_token_num == 4){        // Token = ID
            if (compare_strings(tl->my_lexeme, integer) == 0){
                tl->my_lexeme_num = 1;    // Terminal will be type integer
            }else if(compare_strings(tl->my_lexeme, doub) == 0){
                tl->my_lexeme_num = 2;    // Terminal will be type double
            }else{
                tl->my_lexeme_num = 3;    // Terminal will be var
            }
        }else if(tl->my_token_num == 5){  // Token = Keyword

            // Binary search keywords array stored in ll1.h
            tl->my_lexeme_num = binary_search(keywords, tl->my_lexeme, 14) + 1;
        }else{                            // Token = OP

            // Set my_lexeme_num to char value of lexeme
            tl->my_lexeme_num = tl->my_lexeme[0];
        }
    }
    // If token is any other type my_lexeme_num is not set as it is never used
}

// A function to find a terminal value given a token lexeme pair
int get_terminal(struct token_lexeme tl){

	// Check token
	switch (tl.my_token_num) {
		// Terminals that are OPERATORS
		case 10:
			switch (tl.my_lexeme_num) {
				case '=':
					return 20;
				case '[':
					return 21;
				case ']':
					return 22;
				case '(':
					return 23;
				case ')':
					return 24;
				case ';':
					return 25;
				case ',':
					return 26;
				case '+':
					return 29;
				case '-':
					return 30;
				case '*':
					return 31;
				case '/':
					return 32;
				case '%':
					return 33;
			}
            break;
		// Terminals that are KEYWORDS
		case 5:
			switch (tl.my_lexeme_num) {
                // and
				case 1:
                    return 35;
                // def
                case 2:
                    return 0;
                // do
                case 3:
                    return 10;
                // else
                case 4:
                    return 7;
                // fed
                case 5:
                    return 1;
                //fi
                case 6:
                    return 8;
                // if
                case 7:
                    return 5;
                // not
                case 8:
                    return 36;
                // od
                case 9:
                    return 11;
                // or
                case 10:
                    return 34;
                // print
                case 11:
                    return 12;
                // return
                case 12:
                    return 13;
                // then
                case 13:
                    return 6;
                // while
                case 14:
                    return 9;
			}
            break;
		// Terminals that are IDs
		case 4:
			switch (tl.my_lexeme_num) {
                // type int
				case 1:
					return 3;
                // type double
				case 2:
					return 4;
                // var
				default:
					return 2;
			}
            break;
		// Terminals that are NUMBERS
		case 9:
            // Number integer
			if(tl.is_int_flag){
				return 27;
			}
            // Number double
			return 28;
		// Less than
		case 6:
			return 14;
		// Greater than
		case 2:
			return 15;
		// Is equal
		case 1:
			return 16;
		// Less than or equal
		case 7:
			return 17;
		// Greater than or equal
		case 3:
			return 18;
		// Not equal
		case 8:
            return 19;
        // Used for final call to epsilon
        case 1000:
            return 37;
        
	}
    return 37;
}

#endif // FUNCTIONS_H