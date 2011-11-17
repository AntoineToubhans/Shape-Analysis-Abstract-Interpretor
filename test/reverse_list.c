#include <stdio.h>


void main(){

  struct list{
    struct list* next;
    int data;
  };
  
  struct list* l;
  l = malloc(16);
  l-> next = malloc(16);
  l-> next-> next = malloc(16);
  /* 
     _SPEC 
        canonicalize;
        forget_inductive_length;
     SPEC_
  */
  struct list* x = NULL;
  struct list* y = NULL;

  while(l !=NULL){
    y = l;
    l = l -> next;
    y -> next = x;
    x = y;
  }
  
}

