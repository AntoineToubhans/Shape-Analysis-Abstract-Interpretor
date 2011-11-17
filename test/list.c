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
  struct list* x = l;
  /* 
     _SPEC 
        canonicalize;
        forget_inductive_length;
     SPEC_
  */

  while(l !=NULL){
    l = l -> next;
  }
  
}

