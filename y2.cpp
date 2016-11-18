#include <iostream>
#include <functional>

using namespace std;

/*
References:
"A Lecture on the 'Why' of 'Y'" by Matthias Felleisen
http://www.ps.uni-sb.de/courses/sem-prog97/material/YYWorks.ps

https://yongweiwu.wordpress.com/2014/12/14/y-combinator-and-cplusplus/#fn-39-10

http://mvanier.livejournal.com/2897.html


*/


//Standard factorial function
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

/*
Assume
T : Type
self_ref_func<T> A;

then
A.fn : function<T(self_ref_func<T>)>

what can you call this function on?
you need another self_ref_func<T>

so assume:
self_ref_func B;

now you can call A.fn(B).
But also:
B.fn : function<T(self_ref_func<T>)>

what can you call B.fn on?
You can't keep creating new 
self_ref_func B2;
self_ref_func_B3;
...
forever

but you can call B.fn on A, because
A : self_ref_func<T>

and you can also call A.fn on A, because
A.fn : function<T(self_ref_func<T>)>

A.fn(A) simulates the untypable (x x)


*/

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

template <typename A, typename B>
function<B(A)> Y_comb(function<function<B(A)>(function<B(A)>)> f)
{
 fn_self_ref r;
 r.fn = [f](fn_self_ref x){
  return f ([x](A y){return x.fn(x)(y);});
 };
 return r.fn(r);
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
 function<int(int)> facY = Y_comb(almost_factorial);
 cout << "factorial(10) = " << factorial(10) << endl;
 cout << "fac(10) = " << fac(10) << endl;
 cout << "facA(10) = " << facA(10) << endl;
 cout << "facY(10) = " << facY(10) << endl;
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
