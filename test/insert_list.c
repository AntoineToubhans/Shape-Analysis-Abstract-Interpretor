#include <stdio.h>


void main(){

  struct list{
    struct list* next;
    int data;
  };

  int x = 42;
  struct list* l_call;
  l_call = malloc(16);
  l_call -> next = malloc(16);
  l_call -> next-> next = malloc(16);
  struct list* l = l_call;
  struct list* r = NULL;
  /* 
     _SPEC 
        canonicalize;
        forget_inductive_length;
     SPEC_
  */
  while(l!=NULL){
    if(l-> next == NULL){
      l-> next = malloc(16);
      l-> next-> data = x;
      l-> next-> next = NULL;
      l = NULL;
    }
    else{
      if(l-> next-> data != x){
	l = l-> next;
      }
      else{
	r = l-> next;
	l-> next = malloc(16);
	l-> next-> data = x;
	l-> next-> next = r;
	l = NULL; 
      }
    }
  }
}

