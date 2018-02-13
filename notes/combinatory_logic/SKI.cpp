#include <iostream>

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

void evaluate(char * e){
 std::cout << "Nothing to see here.\n";
}

int main(int argc, char** argv){
 if(argc < 2){
  std::cout << "Please provide a SKI combinator.\n";
  return false;
 }

 if(argc > 2){
  std::cout << "Just one combinator, please.\n";
  return false;
 }


 if(check(argv[1])){
  evaluate(argv[1]);
 }else{
  std::cout << "Not a valid SKI expression.\n";
 }
}
