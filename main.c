#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

// Suggested values for `true` and `false` to distinguish them from pointers
#define TRUE  0x0000000000000006L
#define FALSE 0x0000000000000002L

#define BOA_MIN (- (1L << 62))
#define BOA_MAX ((1L << 62) - 1)

extern int64_t our_code_starts_here(int64_t* the_heap, int64_t input_val) asm("our_code_starts_here");
extern int64_t print(int64_t input_val) asm("print");
extern void error(int64_t val) asm("error");

extern void t_num_error() asm("t_num_error");
extern void t_bool_error() asm("t_bool_error");
extern void overflow_error() asm("overflow_error");

int64_t print(int64_t val) {
  if(val & 1) {
    int64_t val_boa =  (val-1)/2;
    if(val_boa < BOA_MIN || val_boa > BOA_MAX) {
      overflow_error();
    }
    else printf("%lld\n", val_boa);
  }
  else if( val == TRUE ) {
	  printf("true\n");
  }
  else if ( val == FALSE ) {
	  printf("false\n");
  }
  else {
	  printf("Got unrepresentable value: %lld", val);
  }
}

void t_num_error() {
  fprintf(stderr, "expected a number");
  exit(1);
}

void overflow_error() {
  fprintf(stderr, "overflow");
  exit(1);
}

void t_bool_error() {
  fprintf(stderr, "expected a bool");
  exit(1);
}

void error(int64_t error_code) {
  if(error_code == 0) {
    overflow_error();
  }
  else if(error_code == 1) {
    t_num_error();
  }
  else if(error_code == 2) {
    t_bool_error();
  }
	else {
    fprintf(stderr, "Unknown Identifier");
	  exit(1);
  }
}


int main(int argc, char** argv) {
  int64_t input_val;
  // FILL IN YOUR CODE FROM HERE
  if(argc > 1) {
    if( strcmp(argv[1], "true") == 0 ) { 
        fprintf(stderr, "input must be a number");
        exit(1);
    } 
    else if (strcmp(argv[1],"false") == 0 ) {
        fprintf(stderr, "input must be a number");
        exit(1);
    }
    else {
      char *eptr;
      long long ll_input = strtoll(argv[1], &eptr, 10);
      if(*eptr != '\0') {
        fprintf(stderr, "input must be a number");
        exit(1);
      }
      else if( errno == ERANGE ) {
        fprintf(stderr, "input is not a representable number");
        exit(1);
      }
      else {
        input_val = 1+(ll_input*2);
        if(ll_input  > BOA_MAX  ) {
           fprintf(stderr, "input is not a representable number input:%lld %lld", BOA_MAX, ll_input);
           exit(1);
        }
        else if (ll_input <= BOA_MIN ) {
           fprintf(stderr, "input is not a representable number input:%lld %lld", BOA_MIN, ll_input);
           exit(1);
        }
        
      }
    }
  }
  else { 
    input_val = 1;
  }
  
  // YOUR CODE ENDS HERE
  int64_t* the_heap = calloc(10000, sizeof(int64_t));
  int64_t result = our_code_starts_here(the_heap, input_val);
  print(result);
  return 0;
}
