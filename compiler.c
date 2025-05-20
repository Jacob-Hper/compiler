/*
* CP471 Compiler Final: Full Compiler
* Overview:
* Implements a lexical analyzer using a state transition table approach as well as a syntax analyzer using an Abstract Syntax tree 
* and performs Semantic analysis in line with Syntax analysis. Finally, produces a three adress code translation of the source code.
* Processes source code files to generate a symbol table and error log.
* 
* Inputs:
* - Source file (example.cp) containing code to analyze
* 
* Outputs:
* - symbol_table_lex.txt: Contains recognized tokens and their types
* - symbol_table_syn.txt: Contains production information
* - symbol_table_sem.txt: Contains scope information
* - tac.txt:              Contains the three adress code transaltion of the source code
* - error.txt: Records lexical, syntactical, and semantic errors encountered
*
* Author: Jacob Harper, 201830230
*
* Date: April 22 2025
*
* Dependencies:
* - functions.h (contains structure and function definintions that can be stored separately from global variables and other header files)
* - resources.h (contains tables required by this program including state machine and LL1 table, as well as several which hold imporant variable names)
*/
/******************************** Header Imports ********************************/
#include <stdio.h>
#include <stdlib.h>
#include "resources.h"
#include "functions.h"

/******************************** Global Variables ********************************/
/**************** Lexical ****************/
//Flags
int pushback_char = -1;                      // Pushback flag is for rereading a char at the end of a token
int checkNegativeFlag = 0;                   // Check Negative flag is for checking the difference between a leading +- and the operators +,-

// Global Variables
#define BUFFER_SIZE 2048
#define LEXEME_SIZE 256

// Double Buffer System Variables
char buffer1[BUFFER_SIZE];
char buffer2[BUFFER_SIZE];
int current_buffer = 1;                                // Buffer number flag
size_t index_buffer = 0;                               // Index in current buffer
size_t size_buffer1 = 0;                               // Chars remaining unread in buffer1
size_t size_buffer2 = 0;                               // Chars remaining unread in buffer2

/**************** Syntax ****************/
// Initialize node pointers for AST Traversal
struct node* root;                                     // Points to current node of AST
struct node* next;                                     // Points to next node when traversing down AST

/**************** Semantic ****************/
// Flags
int function_flag = 0;                                 // Tracking where the program is in the function definititon process
int type_flag = -1;                                    // Tracks the current type for type checking
int var_type = -1;                                     // Tracks the initializing type for creating local variables

// Global Variables
int type_depth = 0;                                    // Tracks the current depth on the AST ffrom the start of a type check
char* hold_lexeme;                                     // <id> held until we can disambiguate a var from a function call

// Instantiate global structs
struct global global_scope;                            // Holds lowest level scope and also pointers to all function definitions
struct check_functions* function_call_stack = NULL;    // Struct for type checking params when a function call is passed as a param of a function

/******************************** Function Definitions ********************************/
// These cannot be moved to the functions header file as they rely on stdlib or some global value defined in this file

/**************** "Constructors" ****************/
// Generates a new scope
void create_new_scope(
    struct scope** current_scope,
    int line_number,
    const char* start_lexeme,
    FILE* symbol_table_sem
) {
    // Create a new scope
    struct scope* new_scope = malloc(sizeof(struct scope));
    
    // Initialize the new scope
    new_scope->parent_scope = *current_scope;
    new_scope->local_vars = NULL;  // Assuming variables are initialized to NULL
    new_scope->num_vars = 0;     // Assuming var_count starts at 0
    
    // Update the current scope pointer
    *current_scope = new_scope;

    // Print scope information to symbol table
    fprintf(symbol_table_sem, "## Scope ##\nLine: %d, Start Lexeme: %s\n", 
            line_number, start_lexeme);
}

// Generates a new function
void new_function(int line_number, struct function** new_funct, struct scope** current_scope, FILE* symbol_table){
    // Create new function
    *new_funct = malloc(sizeof(struct function));
    (*new_funct)->line = line_number;
    (*new_funct)->num_params = 0;
    (*new_funct)->return_type = -1;
    (*new_funct)->lexeme = NULL;
    (*new_funct)->param_types = NULL;
    create_new_scope(current_scope, line_number, "fed", symbol_table);
    (*new_funct)->my_scope = *current_scope;

    // Append new function to the end of global_scope.functions
    struct function *temp;
    global_scope.num_functions++;

    // Allocate memory for the updated array of functions
    if (global_scope.num_functions == 1) {
        // First function - initial allocation
        temp = malloc(sizeof(struct function));
    } else {
        // Subsequent functions - reallocation preserving existing functions
        temp = malloc(sizeof(struct function) * global_scope.num_functions);
        // Copy existing functions to the new memory location
        for (int i = 0; i < global_scope.num_functions - 1; i++) {
            temp[i] = global_scope.functions[i];
        }
        // Free the old memory to prevent memory leaks
        free(global_scope.functions);
    }
    // Add the new function at the end
    temp[global_scope.num_functions - 1] = (**new_funct);
    global_scope.functions = temp;
}

/**************** Struct editing functions ****************/
// SEMANTIC
// Adds a required parameter to a function
void add_param(struct function** this_funct, int type){
    (*this_funct)->num_params++;
    int* temp;
    if((*this_funct)->num_params == 1){
        temp = malloc(sizeof(char));
    }else{
        temp = malloc(sizeof(int) * (*this_funct)->num_params);
        for(int i = 0; i < (*this_funct)->num_params - 1; i++){
            temp[i] = (*this_funct)->param_types[i];
        }
        free((*this_funct)->param_types);
    }

    temp[(*this_funct)->num_params - 1] = type;
    (*this_funct)->param_types = temp;
}

// Adds a local variable to a scope
void add_var(struct scope** scope_ptr, struct variable new_var){
    struct scope* this_scope = *scope_ptr;
    this_scope->num_vars++;
    struct variable* temp;
    if(this_scope->num_vars == 1){
        temp = malloc(sizeof(struct variable));
    }else{
        temp = malloc(sizeof(struct variable) * this_scope->num_vars);
        for(int i = 0; i < this_scope->num_vars - 1; i++){
            temp[i] = this_scope->local_vars[i];
        }
        free(this_scope->local_vars);
    }

    temp[this_scope->num_vars - 1] = new_var;
    this_scope->local_vars = temp;
}

// Adds a function to the function call stack (for function calls passed as params to functions)
void add_function(struct function* function_call, struct check_functions* function_call_stack){
    // For a first function call
    if (function_call_stack->functions == NULL) {
        // Initializes new arrays for functions and indeces, sets num_unctions to 1
        function_call_stack->functions = malloc(sizeof(struct function*));
        function_call_stack->indeces = malloc(sizeof(int));
        function_call_stack->num_functions = 1;
        // Assigns values to first index of arrays
        function_call_stack->functions[0] = function_call;
        function_call_stack->indeces[0] = 0;
        return;
    }

    // For function calls passed as a param to a function
    int new_size = function_call_stack->num_functions + 1;
    function_call_stack->functions = realloc(function_call_stack->functions, sizeof(struct function*) * new_size);
    function_call_stack->indeces = realloc(function_call_stack->indeces, sizeof(int) * new_size);

    // Memory error
    if (function_call_stack->functions == NULL || function_call_stack->indeces == NULL) {
        printf("Error: Memory fault in add_function() call\n");
        return;
    }

    // Updates arrays with new function call and an index of 0
    function_call_stack->functions[function_call_stack->num_functions] = function_call;
    function_call_stack->indeces[function_call_stack->num_functions] = 0;
    function_call_stack->num_functions = new_size;
}

// Removes the most recently added function from the function call stack
void remove_function(struct check_functions* function_call_stack) {
    // Check if function_call_stack is NULL
    if (function_call_stack == NULL) {
        printf("Error: NULL function_call_stack in remove_function() call\n");
        return;
    }

    // Check if there are any functions to remove
    if (function_call_stack->num_functions <= 0) {
        printf("Error: No functions to remove in function_call_stack\n");
        return;
    }

    // Decrement the number of functions
    function_call_stack->num_functions--;

    // If we've removed all functions, free the arrays and reset them to NULL
    if (function_call_stack->num_functions == 0) {
        free(function_call_stack->functions);
        free(function_call_stack->indeces);
        function_call_stack->functions = NULL;
        function_call_stack->indeces = NULL;
    } else {
        // Otherwise, resize the arrays to fit the reduced number of functions
        function_call_stack->functions = realloc(function_call_stack->functions, 
                                               sizeof(struct function*) * function_call_stack->num_functions);
        function_call_stack->indeces = realloc(function_call_stack->indeces, 
                                             sizeof(int) * function_call_stack->num_functions);
        
        // Check if realloc was successful
        if (function_call_stack->functions == NULL || function_call_stack->indeces == NULL) {
            printf("Error: Memory fault in remove_function() call\n");
            return;
        }
    }
}

// SYNTAX
// Function to create production nodes for current node
void insert(int* vals, struct node* root){
    // Set values of root and allocate memory for children pointers 
    int size = vals[0];
    root->size = size;
    root->children = (struct node**)malloc(size * sizeof(struct node*));
    struct node* temp;

    // For each production in array vals create a node with that value
    for(int i = 1; i <= size; i++){
        // Allocate memory for temp node
        temp = malloc(sizeof(struct node));

        // Set terminal flag for temp
        if(vals[i] < 0){        // Variables are stored in productions as negative integer values
            temp->value = -vals[i];
            temp->terminal_flag = 0;

        }else{                  // Terminals are stored in productions as possitive integer values
            temp->value = vals[i];
            temp->terminal_flag = 1;

        }

        // Set temps values as defaults and set root->child i-1 to be temp
        temp->index = 0;
        temp->parent = root;
        temp->children = NULL;
        root->children[i-1] = temp;
    }

}

// Delete tree function (frees memory and deletes all node in tree)
void delete_tree(struct node* root) {
    // Error handling NULL root
    if (root == NULL) {
        printf("Error: Null passed to delete_tree");
        return;
    }
    
    // Recursively delete all children
    if (root->children != NULL) {
        for (int i = 0; i < root->size; i++) {
            if (root->children[i] != NULL) {
                delete_tree(root->children[i]);
            }
        }
        root->children = NULL;
        free(root->children);
    }

    
    // Reset all remaining values of root
    root->value = 0;
    root->size = 0;
    root->terminal_flag = 0;
    root->index = 0;
    root->parent = NULL;  
    free(root);
    root = NULL;
}

/**************** Various print functions ****************/
// TAC

/******************************************** EXPERIMENTAL, TAC PRINTING ********************************************/


char tac_buffer[4096];
int tac_buffer_index = 0;

struct tac_context{
    int memory;
    int temp_counter;
    int label_counter;
    int stack_mem;
    int tac_type;
};

struct tac_context* tacc;

char* gen_bool_exp(char* l, int bool_type, char* r, struct tac_context** tacc){

    char* str = "";
    char* temp1 = "";
    char* temp2 = "";
    int write;
    switch (bool_type) {
        case 14:

            temp1 = malloc(sizeof(char) * 10);
            snprintf(temp1, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s > %s\n", temp1, l, r);


            tac_buffer_index += write;

            temp2 = malloc(sizeof(char) * 10);
            snprintf(temp2, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s == %s\n", temp2, l, r);

            tac_buffer_index += write;

            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s || %s\n", str, l, r);

            tac_buffer_index += write;

            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 12;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 24;
            }


            break;
        case 17:
            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s > %s\n", str, l, r);

            tac_buffer_index += write;
            
            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 4;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 8;
            }

            break;
        
        case 16:
            temp1 = malloc(sizeof(char) * 10);
            snprintf(temp1, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s > %s\n", temp1, l, r);

            tac_buffer_index += write;

            temp2 = malloc(sizeof(char) * 10);
            snprintf(temp2, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s < %s\n", temp2, l, r);

            tac_buffer_index += write;

            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s || %s\n", str, l, r);

            tac_buffer_index += write;

            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 12;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 24;
            }

            break;
        
        case 15:
            temp1 = malloc(sizeof(char) * 10);
            snprintf(temp1, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s < %s\n", temp1, l, r);

            tac_buffer_index += write;

            temp2 = malloc(sizeof(char) * 10);
            snprintf(temp2, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s == %s\n", temp2, l, r);

            tac_buffer_index += write;

            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s || %s\n", str, l, r);

            tac_buffer_index += write;

            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 12;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 24;
            }

            break;

        case 18:
            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s < %s\n", str, l, r);

            tac_buffer_index += write;
            
            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 4;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 8;
            }

            break;
        
        case 19:
            str = malloc(sizeof(char) * 10);
            snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
            write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s == %s\n", str, l, r);

            tac_buffer_index += write;
            
            if ((*tacc)->tac_type == 1) {
                (*tacc)->memory += 4;
            }
            else if ((*tacc)->tac_type == 0){
                (*tacc)->memory += 8;
            }

            break;
    }
    return str;
}


char* gen_constant(struct node* root, struct tac_context** tacc){
    char* str;
    str = malloc(sizeof(char) * 10);
    snprintf(str, sizeof(str), "t%d", (*tacc)->temp_counter++);

    int write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    %s = %s\n", str, root->lexeme);
    tac_buffer_index += write;



    if (root->value == 27) {
        (*tacc)->memory += 4;
        (*tacc)->tac_type = 1;

    }
    else if (root->value == 28) {
        (*tacc)->memory += 8;
        (*tacc)->tac_type = 0;
    }
    return str;
}

// ????
char* gen_id(struct node* root, struct tac_context** tacc){
    char* value;
    value = copy_string(root->lexeme);
    (*tacc)->tac_type = root->type;
    return value;
}

char* gen_expr(struct node* root, struct tac_context** tacc){
    char* str = "";
    char* temp;
    const char* empty = "";
    if (!root->children || root->terminal_flag == 1){
        if (root->value == 2) {
            str = gen_id(root, tacc);
        }
        else if (root->value == 27 || root->value == 28) {
            str = gen_constant(root, tacc);
        }
        return str;
    }

    char *l, *r, *op, *label;
    int bool_type;
    int write, temp_stack_mem;

    switch (root->value) {
        case 13:
            switch (root->children[0]->value) {
                case 5:     // if statement
                    l = gen_expr(root->children[2], tacc);
                    label = malloc(sizeof(char) * 10);
                    snprintf(label, 10, "L%d", (*tacc)->label_counter++);
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    IFZ  %s Goto %s\n", l, label);
                    tac_buffer_index += write;


                    r = gen_expr(root->children[5], tacc);

                    if (root->children[6]->size > 1) {
                        write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    Goto L%d\n",(*tacc)->label_counter);
                        tac_buffer_index += write;
                    }


                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "%s\n", label);
                    tac_buffer_index += write;
                    
                    if (root->children[6]->size > 1) {
                        r = gen_expr(root->children[6], tacc);
                        write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "L%d\n",(*tacc)->label_counter);
                        tac_buffer_index += write;
                    }


                break;
                case 9:
                    l = gen_expr(root->children[2], tacc);
                    label = malloc(sizeof(char) * 10);
                    snprintf(label, 10, "L%d", (*tacc)->label_counter++);

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "L%d\n", (*tacc)->label_counter);
                    tac_buffer_index += write;

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    IFZ  %s Goto %s\n", l, label);
                    tac_buffer_index += write;
                    

                    r = gen_expr(root->children[5], tacc);

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    Goto L%d\n", (*tacc)->label_counter);
                    tac_buffer_index += write;

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "%s\n", label);
                    tac_buffer_index += write;

                    break;

                case 12:
                    str = gen_expr(root->children[1], tacc);
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    Print %s\n", str);
                    tac_buffer_index += write;
                    break;
                case 13:
                    str = gen_expr(root->children[1], tacc);
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    Return %s\n", str);
                    tac_buffer_index += write;
                
                    break;
                case 30:    // Assignment <var> = <expression>

                    l = gen_expr(root->children[0], tacc);
                    r = gen_expr(root->children[2], tacc);

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    %s = %s\n", l, r);
                    tac_buffer_index += write;


                    break;


                case 37:
                    break;
                
            }
            break;
        case 15:
            if (root->size > 1) {
                if (root->children[1]->size > 1) {
                    r = gen_expr(root->children[1], tacc);
                    if (!compare_strings(r, empty) == 0) {
                        write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    PushParam %s\n", r);
                        tac_buffer_index += write;

                        (*tacc)->stack_mem += 4;
                    }

                }

                l = gen_expr(root->children[0], tacc);
                if (!compare_strings(l, empty) == 0) {
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    PushParam %s\n", l);
                    tac_buffer_index += write;

                    (*tacc)->stack_mem += 4;
                }   

            }

            break;
        
        case 16:
            if (root->size > 1) {
                if (root->children[1]->size > 1) {
                    r = gen_expr(root->children[1], tacc);
                    if (!compare_strings(r, empty) == 0) {
                        write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    PushParam %s\n", r);
                        tac_buffer_index += write;

                        (*tacc)->stack_mem += 4;
                    }

                }

                l = gen_expr(root->children[0], tacc);
                if (!compare_strings(l, empty) == 0) {
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    PushParam %s\n", l);
                    tac_buffer_index += write;

                    (*tacc)->stack_mem += 4;
                }   

            }

            break;
        case 17:
            if (root->size == 2){
                if (root->children[1]->size == 1) {
                    str = root->children[0]->lexeme;
                    (*tacc)->tac_type = root->children[0]->type;
                }
                else {
                    temp_stack_mem = (*tacc)->stack_mem;
                    l = gen_expr(root->children[1], tacc);
                    str = malloc(sizeof(char) * 10);
                    snprintf(str, 10,  "t%d", (*tacc)->temp_counter++);

                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = LCall %s\n", str, root->children[0]->lexeme);
                    tac_buffer_index += write;

                    (*tacc)->tac_type = root->children[0]->type;

                    if ((*tacc)->tac_type == 1) {
                        (*tacc)->memory += 4;
                    }
                    else if ((*tacc)->tac_type == 0){
                        (*tacc)->memory += 8;
                    }
                    
                    int num = ((*tacc)->stack_mem - temp_stack_mem);
                    write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    PopParams %d\n", num);
                    tac_buffer_index += write;

                    (*tacc)->stack_mem -= num;
                }
            }
            else{
                for (int i = 0; i < root->size; i++){
                    str = gen_expr(root->children[i], tacc);
                }
            }
            break;
            
        case 19:   // <Term> (*, /, %) operators

            if (root->children[1]->size > 1){
                l = gen_expr(root->children[0], tacc);
                op = root->children[1]->children[0]->lexeme;
                
                r = gen_expr(root->children[1], tacc);
                

                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
                write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s %s %s\n", str, l, op, r);

                tac_buffer_index += write;
                
                if ((*tacc)->tac_type == 1) {
                    (*tacc)->memory += 4;
                }
                else if ((*tacc)->tac_type == 0){
                    (*tacc)->memory += 8;
                }

            }
            else{
                str = gen_expr(root->children[0], tacc);
            }
            
            break;

        case 20:
            l = gen_expr(root->children[1], tacc);

            if (root->children[2]->size > 1){

                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "t%d", (*tacc)->temp_counter++);

                r = gen_expr(root->children[2], tacc);
                op = root->children[2]->children[0]->lexeme;

                write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s %s %s\n", str, l, op, r);
                tac_buffer_index += write;
                
                if ((*tacc)->tac_type == 1) {
                    (*tacc)->memory += 4;
                }
                else if ((*tacc)->tac_type == 0){
                    (*tacc)->memory += 8;
                }

            }
            else{
                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "%s", l);
            }
            break;

        case 21:    // plus/minus expressions
            if (root->children[1]->size > 1){
                l = gen_expr(root->children[0], tacc);
                op = root->children[1]->children[0]->lexeme;
                r = gen_expr(root->children[1], tacc);

                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "t%d", (*tacc)->temp_counter++);
                write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s %s %s\n", str, l, op, r);

                tac_buffer_index += write;
                
                if ((*tacc)->tac_type == 1) {
                    (*tacc)->memory += 4;
                }
                else if ((*tacc)->tac_type == 0){
                    (*tacc)->memory += 8;
                }

            }
            else{
                str = gen_expr(root->children[0], tacc);
            }
            
            break;

        case 22:
            l = gen_expr(root->children[1], tacc);

            if (root->children[2]->size > 1){
                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "t%d", (*tacc)->temp_counter++);

                r = gen_expr(root->children[2], tacc);
                op = root->children[2]->children[0]->lexeme;
                write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index),  "    %s = %s %s %s\n", str, l, op, r);

                tac_buffer_index += write;

                if ((*tacc)->tac_type == 1) {
                    (*tacc)->memory += 4;
                }
                else if ((*tacc)->tac_type == 0){
                    (*tacc)->memory += 8;
                }
                

            }
            else{
                str = malloc(sizeof(char) * 10);
                snprintf(str, 10, "%s", l);
            }
            break;

        case 23:   // Comparison expressions
            if (root->children[1]->size > 1){
                l = gen_expr(root->children[0], tacc);
                bool_type = root->children[1]->children[0]->children[0]->value;
                r = gen_expr(root->children[1], tacc);

                str = gen_bool_exp(l, bool_type, r, tacc);

            }
            else{
                str = gen_expr(root->children[0], tacc);
            }
        
            break;

        case 24:
            str = gen_expr(root->children[1], tacc);
            break;

        case 30:
            str = root->children[0]->lexeme;
            (*tacc)->tac_type = root->children[0]->type;
            break;

        case 27:    // Expression node
            str = gen_expr(root->children[0], tacc);
            if (root->children[1]->size > 1) {
                char* temp = malloc(sizeof(char) * 10);
                snprintf(temp, 10, "t%d", (*tacc)->temp_counter++);
                write = snprintf((tac_buffer + tac_buffer_index), (sizeof(tac_buffer) - tac_buffer_index), "    %s = !%s\n", temp, str);
                tac_buffer_index += write;
                str = temp;
            }
            break;

        default:
            for (int i = 0; i < root->size; i++){
                temp = gen_expr(root->children[i], tacc);

                if (!compare_strings(temp, empty) == 0) {
                    str = temp;
                }
            }
            break;
    }
    return str;

}

void print_tac_main_aux(struct node* root, struct tac_context** tacc){
    struct node* right;
    // Handle non-terminal nodes
    if (root->terminal_flag == 0) {
        switch (root->value) {
            case 7:
                right = root->children[1];
                if (root->children[0]->children[0]->value == 3) {
                    (*tacc)->memory +=4;

                    while (right->size > 1) {
                        if (right->children[0]->value == 26) {
                            (*tacc)->memory += 4;
                        }
                        right = right->children[1];
                    } 
                }
                else if (root->children[0]->children[0]->value == 4) {
                    (*tacc)->memory += 8;
                    while (right->size > 1) {
                        if (right->children[0]->value == 26) {
                            (*tacc)->memory += 8;
                        }
                        right = right->children[1];
                    }
                }
                break;
            default:
                break;
        }
        
        // Process all children
        for (int i = 0; i < root->size; i++) {
            print_tac_main_aux(root->children[i], tacc);
        }
    }
}

void print_tac_function_aux(struct node* root, struct tac_context** tacc, FILE* tac_table) {  
    struct node* right;
    // Handle non-terminal nodes
    if (root->terminal_flag == 0) {
        switch (root->value) {
            case 1:
                (*tacc)->memory = 0;
                break;
            case 3:
                if (root->children && root->children[0]->children) {
                    // Check if node is terminal 3 (int) or terminal 4 (double)
                    if (root->children[0]->children[0]->value == 3) {
                        (*tacc)->memory += 4;  // Add 4 to memory
                    }
                    else if (root->children[0]->children[0]->value == 4) {
                        (*tacc)->memory += 8;  // Add 8 to memory
                    }
                }
                break;
            case 5:
                fprintf(tac_table, "%s:\n", root->children[0]->lexeme);
                break;
            case 7:
                right = root->children[1];
                if (root->children[0]->children[0]->value == 3) {
                    (*tacc)->memory +=4;

                    while (right->size > 1) {
                        if (right->children[0]->value == 26) {
                            (*tacc)->memory += 4;
                        }
                        right = right->children[1];
                    } 
                }
                else if (root->children[0]->children[0]->value == 4) {
                    (*tacc)->memory += 8;
                    while (right->size > 1) {
                        if (right->children[0]->value == 26) {
                            (*tacc)->memory += 8;
                        }
                        right = right->children[1];
                    }
                }
                break;
            case 11:
                gen_expr(root, tacc);
                fprintf(tac_table, "    BeginFunc %d:\n", (*tacc)->memory);
                fprintf(tac_table, "%s", tac_buffer);
                fprintf(tac_table, "    EndFunc:\n");
                // Empty tac_buffer
                for (int i = 0; i < 4096; i++) {
                    tac_buffer[i] = '\0';
                }
                tac_buffer_index = 0;
                return;
        }
        
        // Process all children
        for (int i = 0; i < root->size; i++) {
            print_tac_function_aux(root->children[i], tacc, tac_table);
        }
    }
}


// Prints the start of a function definition in TAC
void print_tac(struct node* root, struct tac_context** tacc, FILE* tac_table){
    

    // Print functions to tac file
    print_tac_function_aux(root->children[0], tacc, tac_table);


    (*tacc)->memory = 0;
    // Print main to tac file
    fprintf(tac_table, "main:\n");
    print_tac_main_aux(root->children[1], tacc);
    gen_expr(root->children[2], tacc);
    fprintf(tac_table, "    BeginFunc %d:\n", (*tacc)->memory);
    fprintf(tac_table, "%s", tac_buffer);
    fprintf(tac_table, "    EndFunc:\n");

}


/******************************************** EXPERIMENTAL, TAC PRINTING ********************************************/

// SEMANTIC
// Prints function information
void print_function(struct function this_funct, FILE* symbol_table){
    fprintf(symbol_table, "Function Name: %s, Line Number: %d\n", this_funct.lexeme, this_funct.line);
    fprintf(symbol_table, "Params: ");
    for(int i = 0; i < this_funct.num_params; i++){
        if (this_funct.param_types[i] == 1){
            fprintf(symbol_table, "int");
        }else{
            fprintf(symbol_table, "double");
        }

        if (i < (this_funct.num_params - 1)){
            fprintf(symbol_table, ", ");
        }
    }
    fprintf(symbol_table, "\n");
}

// Print local variables of a scope to symbol table
void print_vars(struct scope this_scope, FILE* symbol_table){
    fprintf(symbol_table, "Variables: ");
    for(int i = 0; i < this_scope.num_vars; i++){
        if (this_scope.local_vars[i].variable_type == 1){
            fprintf(symbol_table, "int ");
        }else{
            fprintf(symbol_table, "double ");
        }
        fprintf(symbol_table, "%s", this_scope.local_vars[i].lexeme);
        if (i < (this_scope.num_vars - 1)){
            fprintf(symbol_table, ", ");
        }
    }
    fprintf(symbol_table, "\n");
}

// SYNTAX
// Function to write production to symbol table
void print_values(struct node* root, FILE* symbol_table){
    fprintf(symbol_table, "Production: %s -> ", prod_var[root->value]);
    for(int i = 0; i < root->size; i++){
        if(root->children[i]->terminal_flag > 0){
            fprintf(symbol_table, "%s ", prod_term[root->children[i]->value]);
        }else{
            fprintf(symbol_table, "%s ", prod_var[root->children[i]->value]);
        }
    }
    fprintf(symbol_table, "\n");
}


/**************** Type checking functions ****************/
// Checks if a function call has a return type that is correct for the current context
void function_check(char* funct_name, int line_number, int* type_flag, struct node** root, FILE* error) {
    // Check all functions saved to global scope to see if funct_name exists
    for (int i = 0; i < global_scope.num_functions; i++){
        if (compare_strings(global_scope.functions[i].lexeme, funct_name) == 0) {
            // Variable found, handle type checking
            if (*type_flag == -1) {
                (*type_flag) = global_scope.functions[i].return_type;
            } else if (*type_flag != global_scope.functions[i].return_type) {
                // Type mismatch
                fprintf(error, "Error: Type mismatch, Line: %d, Function '%s' return type doesn't match expression type\n", line_number, funct_name);
            }

            add_function(&(global_scope.functions[i]), function_call_stack);
            (*root)->type = global_scope.functions[i].return_type;
            return; // Function found
        }
    } 

    struct function* null_function;
    null_function = malloc(sizeof(struct function));
    null_function->num_params = 0;
    add_function(null_function, function_call_stack);

    // If not found Undeclared function
    fprintf(error, "Error: Undeclared function, Line %d: '%s' has been called but not declared\n", line_number, funct_name);
}

// Checks if a param matches the expected value for a function call
void param_check(int is_funct, char* param_name, struct scope **current_scope, int line_number, int param_type, FILE* error){
    function_call_stack->indeces[function_call_stack->num_functions - 1] += 1;
    // Param checking for a function
    if (is_funct == 1) {
        // Check all function names in the global scope
        for (int i = 0; i < global_scope.num_functions; i++) {
            if (compare_strings(global_scope.functions[i].lexeme, param_name) == 0) {
                // Variable found, handle type checking
                if (param_type != global_scope.functions[i].return_type) {
                    // Type mismatch
                    fprintf(error, "Error: Parameter type mismatch, Line: %d, Function '%s' retturn type doesn't match parameter type\n", line_number, param_name);
                }
                add_function(&(global_scope.functions[i]), function_call_stack);
                return; // Variable found, no need to continue searching
            }
        }

        struct function* null_function;
        null_function = malloc(sizeof(struct function));
        null_function->num_params = 0;
        add_function(null_function, function_call_stack);

        // If function not found in any global scope
        fprintf(error, "Error: Uninitialized function, Line %d: '%s' has been referenced but not declared\n", line_number, param_name);
    }

    // Param checking for a variable
    else if (is_funct == 0) {
        // Create a new scope pointer to local variables for 
        struct scope* check_scope = *current_scope;

        while (check_scope != NULL){
            // Check all local variables in the current scope
            for (int i = 0; i < check_scope->num_vars; i++) {
                if (compare_strings(check_scope->local_vars[i].lexeme, param_name) == 0) {
                    // Variable found, handle type checking
                    if (param_type != check_scope->local_vars[i].variable_type) {
                        // Type mismatch
                        fprintf(error, "Error: Parameter type mismatch, Line: %d, Variable '%s' doesn't match parameter type\n", line_number, param_name);
                    }
                    return; // Variable found, no need to continue searching
                }
            }
            // If not found in current scope, move up to parent scope
            check_scope = check_scope->parent_scope;
        }
        // If not found in any scope Unintialized variable
        fprintf(error, "Error: Uninitialized variable, Line %d: '%s' has been referenced but not declared\n", line_number, param_name);
    }
    // Error
    else {
        printf("Error: bad value passed to param_check() function\n");
    }
}


// Check current and all parent scopes for a variable, if type_flag is not set set it, print uninitialized and type errors
void scope_check(char* variable_name, struct scope** current_scope, int line_number, int* type_flag, FILE* error){
    // Create a new scope pointer to local variables for 
    struct scope* check_scope = *current_scope;

    while (check_scope != NULL){
        // Check all local variables in the current scope
        for (int i = 0; i < check_scope->num_vars; i++) {
            if (compare_strings(check_scope->local_vars[i].lexeme, variable_name) == 0) {
                // Variable found, handle type checking
                if (*type_flag == -1) {
                    (*type_flag) = check_scope->local_vars[i].variable_type;
                } else if (*type_flag != check_scope->local_vars[i].variable_type) {
                    // Type mismatch
                    fprintf(error, "Error: Type mismatch, Line: %d, Variable '%s' doesn't match expression type\n", line_number, variable_name);
                }

                return; // Variable found, no need to continue searching
            }
        }
        
        // If not found in current scope, move up to parent scope
        check_scope = check_scope->parent_scope;

    }

    // If not found in any scope Unintialized variable
    fprintf(error, "Error: Uninitialized variable, Line %d: '%s' has been referenced but not declared\n", line_number, variable_name);
}

// Handles scope variables and function params
void scope_handling(
    int terminal, 
    int line_number, 
    struct function** current_funct, 
    struct scope** current_scope, 
    struct token_lexeme tl, 
    FILE* symbol_table_sem
) {
    switch(terminal) {
        case 1:  // Handle end of function scope
            if(function_flag == 0) {
                print_vars(**current_scope, symbol_table_sem);
                *current_scope = (*current_scope)->parent_scope;
                fprintf(symbol_table_sem, "End Lexeme: fed\n");
            }
            (*current_funct) = NULL;
            break;
        case 2:
            if (function_flag == 2) {
                if ((*current_funct)->num_params > 0) {
                    char* variable_str = tl.my_lexeme;
                int length2 = 0;
                while(variable_str[length2] != '\0') length2++;

                struct variable* current_var = malloc(sizeof(struct variable));
                current_var->lexeme = malloc(length2 + 1);
                for(int i = 0; i <= length2; i++) {
                    current_var->lexeme[i] = variable_str[i];
                }
                current_var->lexeme[length2] = '\0';
                current_var->line = line_number;
                current_var->variable_type = (*current_funct)->param_types[(*current_funct)->num_params - 1];
                add_var(current_scope, *current_var);
                }
                
            }
            break;
        case 3:   // int type
        case 4:   // double type
            // Function return type
            if (function_flag == 1){
                (*current_funct)->return_type = (terminal == 3) ? 1 : 0;
            }
            break;

        case 24:  // Right bracket ')'
            if(function_flag == 2) {
                print_function(**current_funct, symbol_table_sem);
                function_flag = 0;
                fprintf(symbol_table_sem, "Line: %d, Start Lexeme: def\n", line_number);
            }
            break;

        default:
            // No special handling for other terminals
            break;
    }
}

// Type checking function
void semantic_check(
    int prod,
    int line_number,
    int* type_depth,
    int* type_flag,
    struct token_lexeme tl,
    struct function** current_funct,
    struct scope** current_scope,
    FILE* symbol_table,
    FILE* error
){
    // Increment type check depth if depth > 0 any time we go down the tree
    if (*type_depth > 0){
        (*type_depth)++;
    }
    switch (prod) {
        case 3:     // Produce <fdec> creates a new function
            new_function(line_number, current_funct, current_scope, symbol_table);
            function_flag = 1;
            break;

        case 4:
            add_param(current_funct, var_type);
            global_scope.functions[global_scope.num_functions - 1] = **current_funct;
            break;

        case 8:
            // Manual string length calculation
            char* function_str = tl.my_lexeme;
            int length1 = 0;
            while(function_str[length1] != '\0') length1++;

            if ((*current_funct) != NULL) {
                // Function name declaration
                (*current_funct)->lexeme = malloc(length1 + 1);
                for(int i = 0; i <= length1; i++) {
                    (*current_funct)->lexeme[i] = function_str[i];
                }
                (*current_funct)->lexeme[length1] = '\0';
                global_scope.functions[global_scope.num_functions - 1] = **current_funct;
                function_flag = 2;
            }
            break;
        case 12: 
            var_type = 1;
            break;
        case 13:
            var_type = 0;
            break;
        case 14: // Variable declarations
            // Manual string length calculation
            char* variable_str = tl.my_lexeme;
            int length2 = 0;
            while(variable_str[length2] != '\0') length2++;

            struct variable* current_var = malloc(sizeof(struct variable));
            current_var->lexeme = malloc(length2 + 1);
            for(int i = 0; i <= length2; i++) {
                current_var->lexeme[i] = variable_str[i];
            }
            current_var->lexeme[length2] = '\0';
            current_var->line = line_number;
            current_var->variable_type = var_type;
            add_var(current_scope, *current_var);
            break;

        case 16:
            var_type = -1;
            break;
        
        case 21:    // Produce <var> = <expr> increments depth by two (must be two not one due to how the language works) and scope checks the <id>
            if (*type_depth == 0){
                (*type_depth) += 2;
                scope_check(tl.my_lexeme, current_scope, line_number, type_flag, error);
            }
            break;
        case 29:
        case 31:    // <exp_seq> or <exp_seq'> Produces epsilon, when a function call exists removes a function from the function call stack.
            if (function_call_stack->num_functions > 0) {
                remove_function(function_call_stack);
            }
            break;

        case 32:    // Produce <var><factor'> saves lexeme to either scope check or function check depending on next input
            // Free any previously allocated memory
            if (hold_lexeme != NULL) {
                free(hold_lexeme);
            }

            // Calculate length of the lexeme
            int len = 0;
            while (tl.my_lexeme[len] != '\0') {
                len++;
            }
            
            // Allocate memory for the new lexeme copy
            hold_lexeme = (char *)malloc(len + 1);
            if (hold_lexeme != NULL) {
                // Copy the lexeme character by character
                for (int i = 0; i < len; i++) {
                    hold_lexeme[i] = tl.my_lexeme[i];
                }
                hold_lexeme[len] = '\0'; // Ensure null termination
            }
            break;

        case 35:    // From <factor'> produce (<exp_seq>), this is a function call perform function checking

            // Write some comments
            if (function_call_stack->num_functions > 0) {
                int index = function_call_stack->indeces[function_call_stack->num_functions - 1];
                if (index >= function_call_stack->functions[function_call_stack->num_functions - 1]->num_params){
                    fprintf(error, "Error: Extra param '%s' for function call at line %d\n", hold_lexeme, line_number);
                }
                else{
                    int type = function_call_stack->functions[function_call_stack->num_functions - 1]->param_types[index];
                    param_check(1, hold_lexeme, current_scope, line_number, type, error);
                }
                free(hold_lexeme);
                hold_lexeme = NULL;
                break;
            }
            
            function_check(hold_lexeme, line_number, type_flag, &root, error);
            free(hold_lexeme);
            hold_lexeme = NULL;
            break;

        case 36:    // From <factor'> produce epsilon, this is a variable perform scope checking
            if (function_call_stack->num_functions > 0) {
                int index = function_call_stack->indeces[function_call_stack->num_functions - 1];
                if (index >= function_call_stack->functions[function_call_stack->num_functions - 1]->num_params){
                    fprintf(error, "Error: Extra param '%s' for function call at line %d\n", hold_lexeme, line_number);
                }
                else{
                    int type = function_call_stack->functions[function_call_stack->num_functions - 1]->param_types[index];
                    param_check(0, hold_lexeme, current_scope, line_number, type, error);
                }
                free(hold_lexeme);
                hold_lexeme = NULL;
                break;
            }
            scope_check(hold_lexeme, current_scope, line_number, type_flag, error);
            free(hold_lexeme);
            hold_lexeme = NULL;
            break;

        case 42:
        case 46:
            if (*type_depth == 0) {
                (*type_depth)++;
            }
            break;

        case 65:
            if (*type_flag == -1) {
                (*type_flag) = 1;
            }else if (*type_flag == 0) {
                fprintf(error, "Error: Type mismatch, Line: %d, Variable '%s' doesn't match expression type\n", line_number, tl.my_lexeme);
            }
            break;

        case 66:
            if (*type_flag == -1){
                (*type_flag) = 0;
            }else if (*type_flag == 1){
                fprintf(error, "Error: Type mismatch, Line: %d, Variable '%s' doesn't match expression type\n", line_number, tl.my_lexeme);
            }
            break;

        default:
            break;
    }
}

/**************** AST traversal functions ****************/

// Syntax error handling
struct node* traverse_error(struct node* node, int terminal){
    // Errors will typically start with a Node with no children, return to lowest node with children to check
    while((node->children == NULL || node->index == node->size - 1) && node->parent != NULL){
        node = node->parent;
    }

    // While node is below <progs>
    while(node->parent != NULL){
        // Check each remaining child of node for current terminal
        for(int i = node->index; i < node->size; i++){
            if(node->children[i]->terminal_flag == 1 && node->children[i]->value == terminal){
                // If terminal is found function sets index and returns node
                node->index = i;
                return node;
            }
        }
        // If terminal is not found node returns to lowest node with valid children
        node = node->parent;
        while(node->index == node->size - 1 && node->parent != NULL){
            node = node->parent;
        }
    }

    // If terminal is not in tree current terminal is responsible for the error, return NULL
    return NULL;
}

// Traverse() helper function traverses up tree until it finds the next valid node
struct node* traverse_up(struct node* root, int* type_depth, int* type_flag) {
    // Check if root is NULL
    if (root == NULL) {
        return NULL;
    }
    
    // Check if parent exists before moving up
    if (root->parent == NULL) {
        return root;
    }
    
    // Move up one level
    root = root->parent;
    root->index++;
    
    // Update type_depth and current_type
    if (*type_depth > 0) {
        (*type_depth)--;
    }
    if (*type_depth == 0) {
        *type_flag = -1;
    }
    
    // Continue moving up while we've exhausted all children at the current level
    while (root->index >= root->size) {
        if (root->parent == NULL) {
            // We've reached the top of the tree
            return root;
        }
        
        root = root->parent;
        root->index++;
        
        // Update type_depth and current_type
        if (*type_depth > 0) {
            (*type_depth)--;
        }
        if (*type_depth == 0) {
            *type_flag = -1;
        }
    }
    
    return root;
}

// Tree traversal function
struct node* traverse(
    struct node* root,
    struct node* next,
    struct token_lexeme tl,
    int line_number,
    struct function** current_funct,
    struct scope** current_scope,
    struct variable** current_var,
    FILE* symbol_table,
    FILE* symbol_table_sem,
    FILE* error
){
    // Get terminal from token lexeme
    int terminal = get_terminal(tl);
    
    // Print newly read terminal to symbol table
    fprintf(symbol_table, "TERMINAL: %s \n", prod_term[terminal]);

    // Get initial production rule from ll1
    int prod = ll1_table[terminal][root->value];

    // Traverse tree
    while(1){
        // Check if current production is valid or if root node has children which could produce a valid production with terminal
        if(prod >= 0 || root->index < root->size){
            // Root children is empty, generate production nodes
            if(!root->children){
                insert(productions[prod], root);
                print_values(root, symbol_table);
            }

            // Error handling for invalid root nodes
            if (root->children != NULL && root->index >= 0 && root->index < root->size) {
                // Get next node
                next = root->children[root->index];
                root = next;
                next = NULL;

                /**************** Semantic check ****************/
                if (root->parent->index > 0){ // Semantic check is designed to only perform actions on the first node of a production. For all other nodes treat prod as -1
                    semantic_check(-1, line_number, &type_depth, &type_flag, tl, current_funct, current_scope, symbol_table_sem, error);
                }
                else{
                    semantic_check(prod, line_number, &type_depth, &type_flag, tl, current_funct, current_scope, symbol_table_sem, error);
                }
                /**************** Semantic check ****************/
                
            } else {
                fprintf(error, "Error: Invalid child access\n");
                return root;
            }

            // Check if current production node is a terminal
            if(root->terminal_flag == 1){
                if (root->value == 37){                     // In the case of an epsilon production node
                    // Return to lowest node that still has child productions
                    root = traverse_up(root, &type_depth, &type_flag);

                    // End of file checking
                    if(terminal == 37 && root->value == 0 && root->index >= root->size){
                        fprintf(symbol_table, "EOF\n");
                        // At end of file print global scope
                        fprintf(symbol_table_sem, "## Global Scope ##\n");
                        print_vars(**current_scope, symbol_table_sem);
                        return root;
                    }

                    // Epsilon production does not return root since we have not found an error and we have not matched our terminal, will update production and return to start of while loop

                }else if(root->value == terminal){          // In the case of a correct terminal match
                    // Print terminal match to symbol table
                    fprintf(symbol_table, "Match terminal: %s\n", prod_term[root->value]);

                    // Copy tl my lexeme and type flag to node. Used for generating TAC file
                    root->lexeme = copy_string(tl.my_lexeme);
                    root->type = type_flag;


                    // Return to lowest node that still has child productions
                    root = traverse_up(root, &type_depth, &type_flag);

                    /**************** Semantic check ****************/
                    scope_handling(terminal, line_number, current_funct, current_scope, tl, symbol_table_sem);


                    
                    // Function returns root
                    return root;
                }else{                                      // Catch cases where the systems was expecting a different terminal production. (I believe this is now redundant due to addition of traverse_error function)
                    // Print error to error doc
                    fprintf(error, "Error: expected %s, received %s, at line %d\n", prod_term[terminal], prod_term[root->value], line_number);
                    
                    // Return to lowest node that still has child productions
                    root = traverse_up(root, &type_depth, &type_flag);

                    // Function returns root
                    return root;
                }
            }
            }else{ // If current production is invalid and root has no children that could create a valid production with terminal, handle error
                // Print error information to error doc
                fprintf(error, "Syntax Error: Production %d, Variable %s, Terminal %s, at line %d\n", prod, prod_var[root->value], prod_term[terminal], line_number);

                // Checks if error was caused by the most recent terminal or if it was caused by a previous production
                struct node* recover = traverse_error(root, terminal);

                // If this terminal is the problem skip and carry on
                if(recover == NULL){
                    return root;
                }

                // Else return root to position in tree where this terminal belongs and continue
                root = recover;
                fprintf(symbol_table, "***ERROR RECOVERY***\n");
                fprintf(symbol_table, "Match terminal: %s, Error recovery\n", prod_term[root->children[root->index]->value]);

                // Increment index and adjust position in AST if necessary
                root->index++;
                while(root->index >= root->size){
                    root = root->parent;
                    root->index++;
                }
                // Function returns root
                return root;
                
            }
        // If function has not returned, update production using terminal, root value and ll1 table
        prod = ll1_table[terminal][root->value];
    }
}

/**************** File read for lex function ****************/
// The next character function for the lexical analyzer
int get_next_char(FILE *fp){
    int c;

    // Reread char flaged as pushback
    if (pushback_char != -1) {
        c = pushback_char;
        pushback_char = -1;
        return c;
    }

    // Read char from the current buffer.
    if (current_buffer == 1) {
        if (index_buffer >= size_buffer1) {
            // Buffer1 is exhausted, load buffer2.
            size_buffer2 = fread(buffer2, sizeof(char), BUFFER_SIZE, fp);
            if (size_buffer2 == 0) {
                return EOF;   // No more input.
            }
            current_buffer = 2;
            index_buffer = 0;
        }
        c = buffer1[index_buffer++];
        return c;
    } else {  // current buffer == 2
        if (index_buffer >= size_buffer2) {
            // Buffer2 is exhausted, load buffer1.
            size_buffer1 = fread(buffer1, sizeof(char), BUFFER_SIZE, fp);
            if (size_buffer1 == 0) {
                return EOF;   // No more input.
            }
            current_buffer = 1;
            index_buffer = 0;
        }
        c = buffer2[index_buffer++];
        return c;
    }

    return c;
}


/******************************** MAIN ********************************/
int main(int argc, char *argv[]){

    // Error handling for invalid use of function
    if (argc < 2) {
        fprintf(stderr, "Usage: %s inputFile\n", argv[0]);
        return 1;
    }

    /******************************** Open Files ********************************/
    // Open the input file 
    FILE *input = fopen(argv[1], "r");
    if (!input) {
        perror("Error opening input file");
        return 1;
    }

    // Open/Create the error file
    FILE *error_doc = fopen("error.txt", "w");
    if (!error_doc) {
        fclose(input);             // Close input file
        perror("Error opening error output file");
        return 1;
    }

    // Open/Create the output file (lex)
    FILE *symbol_table_lex = fopen("symbol_table_lex.txt", "w");
    if (!symbol_table_lex) {
        fclose(input);             // Close input file
        fclose(error_doc);         // Close error log file
        perror("Error opening lexical output file");
        return 1;
    }

    // Open/create the output file (syntax)
    FILE *symbol_table_syn = fopen("symbol_table_syn.txt", "w");
    if (!symbol_table_syn) {
        fclose(input);             // Close input file
        fclose(error_doc);         // Close error file
        fclose(symbol_table_lex);  // Close lexical output file
        perror("Error opening syntax output file");
    }

    // Open/create the output file (Semantic)
    FILE *symbol_table_sem = fopen("symbol_table_sem.txt", "w");
    if (!symbol_table_sem) {
        fclose(input);             // Close input file
        fclose(error_doc);         // Close error file
        fclose(symbol_table_lex);  // Close lexical output file
        fclose(symbol_table_syn);  // Close Syntax output file
        perror("Error opening semantic output file");
    }


    /******************************** Initialize Values ********************************/
    // Initialize buffer1
    size_buffer1 = fread(buffer1, sizeof(char), BUFFER_SIZE, input);
    if (size_buffer1 == 0) {
        // If file is empty end program
        fclose(input);
        fclose(error_doc);
        fclose(symbol_table_lex);
        fclose(symbol_table_syn);
        return 0;
    }
    current_buffer = 1;                                              //
    index_buffer = 0;                                                //

    // Initialize the state variables and lexeme storage
    int previous_state = 0;                                          //
    int new_state;                                                   //
    int line_number = 1;                                             //
    char lexeme[LEXEME_SIZE];                                        //
    int lexeme_index = 0;                                            //
    int c;                                                           // Tracks current Character read from file

    // Initialize token lexeme tracker tl
    struct token_lexeme tl;                                          //
    tl.is_int_flag = -1;                                             //
    tl.my_token = "";                                                //
    tl.my_lexeme = "";                                               //
    int terminal;                                                    //

    // Initialize root node
    root = malloc(sizeof(struct node));                              //
    root->children = NULL;                                           //
    root->value = 0;                                                 //
    root->size = 1;                                                  //
    root->terminal_flag = 0;                                         //
    root->index = 0;                                                 //

    // Initialize global scope
    struct scope* current_scope;                                     //
    current_scope = malloc(sizeof(struct scope));                    //
    current_scope->parent_scope = NULL;                              //

    struct global global_scope;                                      //
    global_scope.my_scope = *current_scope;                          //
    global_scope.num_functions = 0;                                  //

    // Other semantic values
    struct variable* current_variable;                               //
    struct function* current_function;                               //
    current_function = NULL;                                         //
    function_call_stack = malloc(sizeof(struct check_functions));    //

    /******************************** Primary Loop ********************************/
    while ((c = get_next_char(input)) != EOF) {

        // Check for non-ASCII chars
        int ascii_val = (int)c;
        if (ascii_val < 0 || ascii_val >= 128) {
            fprintf(error_doc, "Error at line %d: Non-ASCII character encountered (%d)\n", line_number, ascii_val);
            continue;
        }

        // Disambiguates leading +/- uncertainty
        if(checkNegativeFlag != 0 && previous_state == 0 && (ascii_val == 43 || ascii_val == 45)){
            new_state = 8;
        }else{
            // Get new state from transition table
            new_state = transition_table[ascii_val][previous_state];
        }

        // Check for an error transition (state -1)
        if (new_state == -1) {
            if(lexeme_index == 0){
                lexeme[lexeme_index] = c;
                lexeme_index++;
            }
            lexeme[lexeme_index] = '\0';
            fprintf(error_doc, "Error at line %d: Lexical error for lexeme '%s'\n", line_number, lexeme);
            // Reset the state and clear the lexeme buffer
            previous_state = 0;
            lexeme_index = 0;
            if (c == '\n') {
                line_number++;
            }
            continue;
        }

        // Line count increment for error messaging
        if (c == '\n') {
            line_number++;
        }

        // If previous state is non-zero and new state is zero we have reached the end of a token
        if (previous_state != 0 && new_state == 0) {

            // Disambiguate integer & double
            if(previous_state == 12){
                // Case is integer
                tl.is_int_flag = 1;
            }else if(previous_state == 14 || previous_state == 16){
                // Case is double
                tl.is_int_flag = 0;
            }

            // Terminate the lexeme string and set lexeme in tl equal to lexeme
            lexeme[lexeme_index] = '\0';
            tl.my_lexeme = lexeme;

            // Check for keywords set token in tl to token and save token/value pair to symbol table
            const char* token;
            if(previous_state == 9){
                if(binary_search(keywords, lexeme, 14) >= 0){
                    token = "KEYWORD";
                }else{
                    token = "ID";
                }
            }else{
                token = state_tokens[previous_state];
            }
            tl.my_token = (char*)token;
            fprintf(symbol_table_lex, "<%s, %s>\n", token, lexeme);

            /**************** Syntax Analysis ****************/

            // Helper function to get token and lexeme as integer values so we can find terminal using a switch case function
            set_tl_nums(&tl);
            // Traverse abstract syntax tree
            root = traverse(root, next, tl, line_number, &current_function, &current_scope, &current_variable, symbol_table_syn, symbol_table_sem, error_doc);

            /**************** Syntax Analysis ****************/

            // Reset tl for next terminal
            clear_tl(&tl);

            // Check negative flag used to disambiguate numbers with leading +- from the + and - operators
            if(compare_strings(token, "ID") == 0 || compare_strings(token, "NUMBER") == 0){
                checkNegativeFlag = 1;
            }else{
                checkNegativeFlag = 0;
            }
            
            // Reset lexeme buffer
            lexeme_index = 0;

            // In case new char is the start of a new token we pushback c to be re-read
            if(c != '\n'){
                pushback_char = c;
            }

            // Reset the state for the next token
            previous_state = 0;
            continue;
        }

        // Add c to lexeme if new state is not start state
        if (new_state != 0) {
            if (lexeme_index < LEXEME_SIZE - 1) {
                lexeme[lexeme_index++] = c;
            } else {
                fprintf(error_doc, "Error at line %d: Token length exceeded buffer size\n", line_number);
                lexeme_index = 0;
                previous_state = 0;
                continue;
            }
        }

        // New state is now the previous state, continue loop
        previous_state = new_state;
    }

    // At EOF, if a token is in buffer add it to output file
    if (lexeme_index > 0 && previous_state != 0) {
        int cmp = compare_strings(state_tokens[previous_state], "N/A");
        if(cmp == 0){
            fprintf(error_doc, "Error at line %d: Lexical error for lexeme '%s'\n", line_number, lexeme);
        }else{
            // Disambiguate integer & double
            if(previous_state == 12){
                appendInteger(lexeme, &lexeme_index);
                tl.is_int_flag = 1;
            }else if(previous_state == 14 || previous_state == 16){
                appendDouble(lexeme, &lexeme_index);
                tl.is_int_flag = 0;
            }

            // Terminate the lexeme string and set lexeme in tl equal to lexeme
            lexeme[lexeme_index] = '\0';
            tl.my_lexeme = lexeme;

            // Check for keywords set token in tl to token and save token/value pair to symbol table
            const char* token;
            if(previous_state == 9){
                if(binary_search(keywords, lexeme, 14) >= 0){
                    token = "KEYWORD";
                }else{
                    token = "ID";
                }
            }else{
                token = state_tokens[previous_state];
            }
            tl.my_token = (char*)token;
            fprintf(symbol_table_lex, "<%s, %s>\n", token, lexeme);

            /**************** Syntax Analysis ****************/
            // Helper function to get token and lexeme as integer values so we can find terminal using a switch case function
            set_tl_nums(&tl);
            // Traverse abstract syntax tree
            root = traverse(root, next, tl, line_number, &current_function, &current_scope, &current_variable, symbol_table_syn, symbol_table_sem, error_doc);
            
            // Reset tl for next terminal
            clear_tl(&tl);
        }
    }

    // At EOF perform epsilon production on AST to check for syntax errors
    while(root->parent != NULL || root->index < root->size -1){
        tl.my_token_num = 1000;
        root = traverse(root, next, tl, line_number, &current_function, &current_scope, &current_variable, symbol_table_syn, symbol_table_sem, error_doc);
    }


    // Close Files
    fclose(input);
    fclose(error_doc);
    fclose(symbol_table_lex);
    fclose(symbol_table_syn);
    fclose(symbol_table_sem);
    /**************** TAC generation ****************/
    

    // Open/Create the error file
    error_doc = fopen("error.txt", "r");
    if (!error_doc) {
        perror("Error: opening error output file\n");
        return 1;
    }

    // Check if the file is empty
    int first_char = fgetc(error_doc);
    if (first_char == EOF && feof(error_doc)) {
        // error.txt file is empty therefore source code has no errors
        tacc = malloc(sizeof(struct tac_context*));
        //(*tacc) = malloc(sizeof(struct tac_context));
        tacc->memory = 0;
        tacc->temp_counter = 0;
        tacc->label_counter = 0;
        tacc->stack_mem = 0;
        tacc->tac_type = -1;
        // Open/create the output file (Three Address Code)
        FILE* tac_table = fopen("tac.txt", "w");
        if (!tac_table) {
            fclose(error_doc);         // Close error file
            perror("Error opening tac file");
            return 1;
        }

        // TAC functions
        print_tac(root, &tacc, tac_table);


        fclose(tac_table);
    }
    else {
        ungetc(first_char, error_doc); // Return the character to the stream
        printf("Please resolve all errors in error.txt to generate TAC\n");
    }

    // Close error doc
    fclose(error_doc);
    
    // Delete abstract syntax tree
    delete_tree(root);

    return 0;
}