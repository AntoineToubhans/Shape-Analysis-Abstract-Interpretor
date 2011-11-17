#include <stdio.h>


void main(){

  struct dll{
    struct dll* next;
    struct dll* prev;
    int top;
  };

  struct dll* l1;
  
  l1 = malloc(16);

  l1 -> next = malloc(16);
  l1 -> prev = malloc(16);
  l1 -> prev -> prev = malloc(16);

  l1 -> next -> prev = l1;
  l1 -> prev -> next = l1;
  l1 -> prev -> prev -> next = l1 -> prev;
  
  struct dll* l2 = l1;

  /* 
     _SPEC 
        canonicalize;
        forget_inductive_length;
     SPEC_
  */
  while(l2 -> next != NULL){
    l2 = l2 -> next;
  }
  while(l2 -> prev != NULL){
    l2 = l2 -> prev;
  }

 

}
