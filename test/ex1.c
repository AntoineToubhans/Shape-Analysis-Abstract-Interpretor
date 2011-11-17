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
  struct dll* q;
  struct m* t = malloc(4);

  t->id=42;

  l = malloc(24);
  q = malloc(24);

  l -> next = malloc(24);
  l -> prev = malloc(24);
  l -> top = t;

  l -> prev -> prev = q;
  l -> prev -> next = l;
  l -> prev -> top = t;

  l -> next -> prev = l;
  l -> next -> next = malloc(24);
  l -> next -> top = t;

  q -> prev = NULL;
  q -> next = l -> prev;
  q -> top = t;

  l -> next -> next -> prev = l -> next;
  l -> next -> next -> next = NULL;
  l -> next -> next -> top = t;
  
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

  while(x->prev != NULL){
    x=x->prev;
  }


  int z = x -> top -> id;
  //  printf("%i\n",z);

  z = 0;
}
