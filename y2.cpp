#include <iostream>
#include <functional>

using namespace std;

/*
References:
https://yongweiwu.wordpress.com/2014/12/14/y-combinator-and-cplusplus/#fn-39-10

http://mvanier.livejournal.com/2897.html


*/

int factorial(int n){
 if (n == 0) return 1;
 else return n * factorial(n - 1);
}

int fibonacci(int n){
  if (n == 0) return 0;
  else if (n == 1) return 1;
  else return fibonacci(n - 2) + fibonacci(n - 1);
}


template <typename F>
struct self_ref_func {
  function<F(self_ref_func<F>)> fn;
};

typedef function<int(int)> fn_1ord;
typedef function<fn_1ord(fn_1ord)> fn_2ord;
typedef self_ref_func<fn_1ord> fn_self_ref;

fn_1ord identity = [](int x){return x;};

fn_2ord almost_factorial = [](fn_1ord f){
 return [f](int n){
  if (n == 0) return 1;
  else return n * f(n - 1);  
 };
};


function<fn_1ord(fn_2ord)> Y_inf = [](fn_2ord f){
 return f(Y_inf(f));
};

template <typename A, typename B>
function<B(A)> Y(function<function<B(A)>(function<B(A)>)> f)
{
 return f([=](A x) {return Y(f)(x);});
}

int main() {
 //Oops, segmentation fault!
 //function<int(int)> fac_inf = Y_inf(almost_factorial);

 //Delay execution by packaging it inside an extra lambda:
 function<int(int)> fac = Y(almost_factorial);
 function<int(int)> facA = almost_factorial(factorial);
 function<int(int)> fac0 = almost_factorial(identity);
 function<int(int)> fac1 = almost_factorial(almost_factorial(identity));
 function<int(int)> fac2 = almost_factorial(almost_factorial(almost_factorial(identity)));
 function<int(int)> fac3 = almost_factorial(almost_factorial(almost_factorial(almost_factorial(identity))));
 cout << "factorial(10) = " << factorial(10) << endl;
 cout << "fac(10) = " << fac(10) << endl;
 cout << "facA(10) = " << facA(10) << endl;
 cout << "fac0(0) = " << fac0(0) << endl;
 cout << "fac0(1) = " << fac0(1) << endl;
 cout << "fac1(0) = " << fac1(0) << endl;
 cout << "fac1(1) = " << fac1(1) << endl;
 cout << "fac1(2) = " << fac1(2) << endl;
 cout << "fac2(0) = " << fac2(0) << endl;
 cout << "fac2(1) = " << fac2(1) << endl;
 cout << "fac2(2) = " << fac2(2) << endl;
 cout << "fac2(3) = " << fac2(3) << endl;
 cout << "fac3(0) = " << fac3(0) << endl;
 cout << "fac3(1) = " << fac3(1) << endl;
 cout << "fac3(2) = " << fac3(2) << endl;
 cout << "fac3(3) = " << fac3(3) << endl;
 cout << "fac3(4) = " << fac3(4) << endl;
 return 0;
}
