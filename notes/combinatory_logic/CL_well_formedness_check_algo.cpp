bool check(char* e){
 int i = 0;
 int p = 0;
 bool x = false;
 while(e[i] != '\0'){
  if((e[i] == 'S') || (e[i] == 'K') || (e[i] == 'I') || ((e[i] >= 97) && (e[i] <= 122))){
   x = false;
   i++;
   continue;
  }

  if(e[i] == '('){
   x = true;
   p++;
   i++;
   continue;
  }

  if(e[i] == ')'){
   if (x || (p < 1)) return false;
   p--;
   i++;
   continue;
  }
  return false;
 }
 return (p == 0) && (i > 0);
}

/*
Only dependency is that `e` actually be null-terminated.

How can we prove the correctness/security of this implementation?

We need a structure to induct over.
Depth of syntax trees isn't particularly good here because we
don't have our syntax trees yet. How about, length of strings?

How can we analyze the complexity of the algorithm?
How can we analyze the complexity of the underlying problem?
Is our algorithm optimal, given the algorithmic building-blocks
we have available to work with?

How robust is this algorithm?
*Example: if parsing the inputs into syntax trees were incorporated,
then this algorithm might have to change, even though it solves the
isolated problem of checking well-formedness just fine.

Can we analyze the machine code?


---------------------------------------
We start with 3 instructions:
int i = 0;
int p = 0;
bool x = false;

At this point we are storing at least
2*sizeof(int) + sizeof(bool) + strlen(e)*sizeof(char).


*/
