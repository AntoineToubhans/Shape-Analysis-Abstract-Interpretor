#include <stdio.h>


void main(){

  struct m{
    int id;
  };

  struct dll{
    struct dll* next;
    struct dll* prev;
    struct m* top;
  };

  struct dll* l;
  struct m t;

  t.id=42;

  l = malloc(24);

  l -> next = malloc(24);
  l -> prev = malloc(24);
  l -> top = &t;

  l -> prev -> prev = malloc(24);
  l -> prev -> next = l;
  l -> prev -> top = &t;

  l -> next -> prev = l;
  l -> next -> next = NULL;
  l -> next -> top = &t;

  l -> prev -> prev -> prev = NULL;
  l -> prev -> prev -> next = l -> prev;
  l -> prev -> prev -> top = &t;
  
  /* 
     _SPEC 
        canonicalize;
        forget_inductive_length;
     SPEC_
  */

  struct dll* x = l;

  while(x->next != NULL){
    x=x->next;
  }

  int z = x -> top -> id;
  //  printf("%i\n",z);

  z = 0;
}
