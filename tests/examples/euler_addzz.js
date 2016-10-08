print = console.log
trace = print
document = {writeln: print}

function printterm(term) {
        if (typeof(term) == 'undefined') return ''
        if (typeof(term.args) == 'undefined') return ''
	if (term.args.length == 0) return term.pred;
	return term.pred+'('+printterm(term.args[0]) + ',' + printterm(term.args[1])+')';
}

function prints(s) {
	if (typeof(s) == 'undefined' || s.length == 0) return '{}'
	var r = '';
	for (var x in s)
		r += x + ':' + printterm(s[x]) + ',';
	return r
}
step = 1

function prove(goal, maxNumberOfSteps) {
  var queue = [{rule:goal, src:0, ind:0, parent:null, env:{}, ground:[]}]
  //if (typeof(evidence) == 'undefined') evidence = {}
  while (queue.length > 0) {
    //console.log(queue.length)
    var c = queue.pop()
    //console.log(JSON.stringify(c.rule.head))
    if(step % 1000 == 0) {
      console.log("step",step)
    }
    if (typeof(c.rule.head.args) != 'undefined') 
	document.writeln( step + ' ' + printterm(evaluate(c.rule.head,c.env)) )
    else document.writeln(step + ' ' + '{}')
    document.writeln(step + ' FSUB:' + prints(c.env));
    document.writeln(step + ' LEN:' + queue.length);
	document.writeln('POP QUEUE\n' + JSON.stringify(c.rule.head) + '\n')
    var g = aCopy(c.ground)
    step++
    if (maxNumberOfSteps != -1 && step >= maxNumberOfSteps) return ''
    if (c.ind >= c.rule.body.length) {
      if (c.parent == null) {
        for (var i = 0; i < c.rule.body.length; i++) {
          var t = evaluate(c.rule.body[i], c.env)
          if (typeof(evidence[t.pred]) == 'undefined') evidence[t.pred] = []
          evidence[t.pred].push({head:t, body:[{pred:'GND', args:c.ground}]})
        }
        continue
      }
      if (c.rule.body.length != 0) g.push({src:c.rule, env:c.env})
      var r = {rule:{head:c.parent.rule.head, body:c.parent.rule.body}, src:c.parent.src, ind:c.parent.ind, 
               parent:c.parent.parent != null ? new copy(c.parent.parent) : null, env:new copy(c.parent.env), ground:g}
      unify(c.rule.head, c.env, r.rule.body[r.ind], r.env, true)
      r.ind++
      queue.push(r)
      if (typeof(r.rule) != 'undefined' && typeof(r.rule.head) != 'undefined' && typeof(r.rule.head.pred) != 'undefined' ) 
	document.writeln('PUSH QUEUE ' + printterm(evaluate(r.rule.head, r.env)))
	else document.writeln('PUSH QUEUE')
      continue
    }
    var t = c.rule.body[c.ind]
    document.writeln( 'Tracking back from ' + printterm(t) )
    var b = -1;//builtin(t, c)
    if (b == 1) {
      g.push({src:{head:evaluate(t, c.env), body:[]}, env:{}})
      var r = {rule:{head:c.rule.head, body:c.rule.body}, src:c.src, ind:c.ind, parent:c.parent, env:c.env, ground:g}
      r.ind++
      queue.push(r)
      if (typeof(trace) != 'undefined') document.writeln('PUSH QUEUE\n' + JSON.stringify(r.rule) + '\n')
      continue
    }
    else if (b == 0) continue
    if (cases[t.pred] == null) continue
    var src = 0
    document.writeln(step + ' TT:' + printterm(t));
    for (var k = 0; k < cases[t.pred].length; k++) {
      var rl = cases[t.pred][k]
      src++
      var g = aCopy(c.ground)
      if (rl.body.length == 0) g.push({src:rl, env:{}})
      var r = {rule:rl, src:src, ind:0, parent:c, env:{}, ground:g}
      if (unify(t, c.env, rl.head, r.env, true)) {
        var ep = c  // euler path
        while (ep = ep.parent) if (ep.src == c.src && unify(ep.rule.head, ep.env, c.rule.head, c.env, false)) break
        if (ep == null) {
          queue.unshift(r)
      if (typeof(r.rule) != 'undefined' && typeof(r.rule.head) != 'undefined' && typeof(r.rule.head.pred) != 'undefined' ) 
	document.writeln('PUSH QUEUE ' + printterm(evaluate(r.rule.head, r.env)))
	else document.writeln('PUSH QUEUE')
          if (typeof(trace) != 'undefined') document.writeln('EULER PATH UNSHIFT QUEUE\n' + JSON.stringify(r.rule) + '\n')
        }
      }
    }
  }
  print('FAIL')
}

function unify(s, senv, d, denv, f) {
//  if (typeof(trace) != 'undefined' && f) 
var r = false, ns=false;
  if (isVar(s.pred)) {
    var sval = evaluate(s, senv)
    if (sval != null) r = unify(sval, senv, d, denv, f)
    else r = true
  }
  else if (isVar(d.pred)) {
    var dval = evaluate(d, denv)
    if (dval != null) r = unify(s, senv, dval, denv, f)
    else {
      if (f != null) {
	denv[d.pred] = evaluate(s, senv)
	ns = true
	}
      r = true
    }
  }
  else if (s.pred == d.pred && s.args.length == d.args.length) {
    for (var i = 0; i < s.args.length; i++) if (!unify(s.args[i], senv, d.args[i], denv, f)) { r = false; break; }
    r = true
  }
  else {
    if (f && typeof(trace) != 'undefined') document.writeln('FAILED TO UNIFY ' + printterm(s) + ' WITH ' + printterm(d))
    if (f && typeof(denv) != 'undefined') document.writeln('DFSUB ' + prints(denv))
    r = false
  }
document.writeln(step + ' UNIFY ' + /*JSON.stringify*/printterm(s) + ' WITH ' + /*JSON.stringify*/printterm(d) )
    if (f && typeof(senv) != 'undefined') document.writeln('SSUB ' + prints(senv))
    else if (f) document.writeln('SSUB')
    if (f && typeof(denv) != 'undefined') document.writeln('DSUB ' + prints(denv))
    else if (f) document.writeln('DSUB')
 if (ns)   	document.writeln('NEW SUB ' + d.pred + '=' + printterm(denv[d.pred]) + ' DURING ' + printterm(s) + '|' + printterm(d) + '|' + prints(senv) + '|' + prints(denv))
  return r;
}

function evaluate(t, env) {
  if (isVar(t.pred)) {
    var a = env[t.pred]
    if (a != null) return evaluate(a, env)
    else return null
  }
  else if (t.args.length == 0) return t
  else {
    var n = []
    for (var i = 0; i < t.args.length; i++) {
      var a = evaluate(t.args[i], env)
      if (a != null) n.push(a)
      else n.push({pred:t.args[i].pred, args:[]})
    }
    return {pred:t.pred, args:n}
  }
}

function isVar(s) { return s.charAt(0) == '?' }
function aCopy(t) { var a = new Array(); for (var i = 0; i < t.length; i++) a[i] = t[i]; return a }
function copy(t) { for (var i in t) this[i] = t[i] }
// Euler proof mechanism -- Jos De Roo
// $Id: Euler4.js 1398 2007-07-20 16:41:33Z josd $

function builtin(t, c) {
  if (t.pred == 'GND') return 1
  var t0 = evaluate(t.args[0], c.env)
  var t1 = evaluate(t.args[1], c.env)
  if (t.pred == 'log:equalTo') {
    if (t0 != null && t1 != null && t0.pred == t1.pred) return 1
    else return 0
  }
  else if (t.pred == 'log:notEqualTo') {
    if (t0 != null && t1 != null && t0.pred != t1.pred) return 1
    else return 0
  }
  else if (t.pred == 'log:semantics') {
    if (typeof(document) == 'undefined') {
      defineClass('euler.Support')
      eval('var s = ' + new Support().fromWeb(t0.pred));
    }
    else {
      var r = window.XMLHttpRequest?new XMLHttpRequest():new ActiveXObject('Msxml2.XMLHTTP')
      r.open('get', t0.pred, false)
      r.send(null)
      if (r.status == 200) eval('var s = ' + r.responseText)
    }
    if (unify(s, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:absoluteValue') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = Math.abs(parseFloat(t0.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:cos') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = Math.cos(parseFloat(t0.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else if (t1 != null && !isVar(t1.pred)) {
      var a = Math.acos(parseFloat(t1.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[0], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:degrees') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = parseFloat(t0.pred) * 180 / Math.PI
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else if (t1 != null && !isVar(t1.pred)) {
      var a = parseFloat(t0.pred) * Math.PI / 180
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[0], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:equalTo') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) == parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:greaterThan') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) > parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:lessThan') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) < parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:notEqualTo') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) != parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:notLessThan') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) >= parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:notGreaterThan') {
    if (t0 != null && t1 != null && parseFloat(t0.pred) <= parseFloat(t1.pred)) return 1
    else return 0
  }
  else if (t.pred == 'math:difference' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a -= parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:exponentiation' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) var a = Math.pow(a, parseFloat(evaluate(ti.args[0], c.env).pred))
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:integerQuotient' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a /= parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:Math.floor(a).toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:negation') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = -parseFloat(t0.pred)
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else if (t1 != null && !isVar(t1.pred)) {
      var a = -parseFloat(t1.pred)
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[0], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:product' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a *= parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:quotient' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a /= parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:remainder' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a %= parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:rounded') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = Math.round(parseFloat(t0.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:sin') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = Math.sin(parseFloat(t0.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else if (t1 != null && !isVar(t1.pred)) {
      var a = Math.asin(parseFloat(t1.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[0], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'math:sum' && t0 != null) {
    var a = parseFloat(evaluate(t0.args[0], c.env).pred)
    for (var ti = t0.args[1]; ti.args.length != 0; ti = ti.args[1]) a += parseFloat(evaluate(ti.args[0], c.env).pred)
    if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'math:tan') {
    if (t0 != null && !isVar(t0.pred)) {
      var a = Math.tan(parseFloat(t0.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[1], c.env, true)) return 1
    }
    else if (t1 != null && !isVar(t1.pred)) {
      var a = Math.atan(parseFloat(t1.pred))
      if (unify({pred:a.toString(), args:[]}, c.env, t.args[0], c.env, true)) return 1
    }
    else return 0
  }
  else if (t.pred == 'rdf:first' && t0 != null && t0.pred == '.' && t0.args.length != 0) {
    if (unify(t0.args[0], c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'rdf:rest' && t0 != null && t0.pred == '.' && t0.args.length != 0) {
    if (unify(t0.args[1], c.env, t.args[1], c.env, true)) return 1
    else return 0
  }
  else if (t.pred == 'a' && t1 != null && t1.pred == 'rdf:List' && t0 != null && t0.pred == '.') return 1
  else if (t.pred == 'a' && t1 != null && t1.pred == 'rdfs:Resource') return 1
  else return -1
}

cases = {
  "": []
}
evidence = {}
step=0

obj = 
[
        {
                "":[{head:{},body:[{pred:"add",args:[{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"?q",args:[]}]}]}
]},     {
                "a":[{head:{pred:"a",args:[{pred:"z",args:[]},{pred:"nat",args:[]}]},body:[]},
{head:{pred:"a",args:[{pred:"?y",args:[]},{pred:"nat",args:[]}]},body:[{pred:"a",args:[{pred:"?x",args:[]},{pred:"nat",args:[]}]},{pred:"succ",args:[{pred:"?x",args:[]},{pred:"?y",args:[]}]}]},
{head:{pred:"a",args:[{pred:"X",args:[]},{pred:"nat",args:[]}]},body:[]},
{head:{pred:"a",args:[{pred:"Y",args:[]},{pred:"nat",args:[]}]},body:[]}
]},     {
                "succ":[{head:{pred:"succ",args:[{pred:"z",args:[]},{pred:"o",args:[]}]},body:[]},
{head:{pred:"succ",args:[{pred:"o",args:[]},{pred:"two",args:[]}]},body:[]}
]},     {
                "add":[{head:{pred:"add",args:[{pred:".",args:[{pred:"?y",args:[]},{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]},body:[{pred:"add",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"?y",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]}]},
{head:{pred:"add",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]},body:[{pred:"eq",args:[{pred:"?z",args:[]},{pred:"?x",args:[]}]}]},
{head:{pred:"add",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"o",args:[]},{pred:".",args:[]}]}]},{pred:"?y",args:[]}]},body:[{pred:"a",args:[{pred:"?x",args:[]},{pred:"nat",args:[]}]},{pred:"succ",args:[{pred:"?x",args:[]},{pred:"?y",args:[]}]}]},
{head:{pred:"add",args:[{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"z",args:[]}]},body:[]},
{head:{pred:"add",args:[{pred:".",args:[{pred:"X",args:[]},{pred:".",args:[{pred:"Y",args:[]},{pred:".",args:[]}]}]},{pred:"S",args:[]}]},body:[]}
]},     {
                "mul":[{head:{pred:"mul",args:[{pred:".",args:[{pred:"?y",args:[]},{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]},body:[{pred:"mul",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"?y",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]}]},
{head:{pred:"mul",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]},body:[{pred:"eq",args:[{pred:"?z",args:[]},{pred:"z",args:[]}]}]},
{head:{pred:"mul",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"o",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]},body:[{pred:"eq",args:[{pred:"?z",args:[]},{pred:"?x",args:[]}]}]},
{head:{pred:"mul",args:[{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"z",args:[]}]},body:[]},
{head:{pred:"mul",args:[{pred:".",args:[{pred:"X",args:[]},{pred:".",args:[{pred:"Y",args:[]},{pred:".",args:[]}]}]},{pred:"M",args:[]}]},body:[]}
]},     {
                "eq":[{head:{pred:"eq",args:[{pred:"?z",args:[]},{pred:"z",args:[]}]},body:[{pred:"mul",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]}]},
{head:{pred:"eq",args:[{pred:"?z",args:[]},{pred:"?x",args:[]}]},body:[{pred:"mul",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"o",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]}]},
{head:{pred:"eq",args:[{pred:"?z",args:[]},{pred:"?x",args:[]}]},body:[{pred:"add",args:[{pred:".",args:[{pred:"?x",args:[]},{pred:".",args:[{pred:"z",args:[]},{pred:".",args:[]}]}]},{pred:"?z",args:[]}]}]}
]}]



function printobj(o) {
  if(o.head) {
    console.log("{"); printobj(o.head); console.log("} <= {");
    for(var i in o.body) {
      printobj(o.body[i]); console.log(".");
    } console.log("}.");
  }
  else if(o.pred) {
    console.log(o.pred, "(")
    for(var a in o.args) {
      console.log(o.args[a])
    } console.log(")")
  }
  else console.log(o);
}

if (arguments.length == 0) print("Usage: java euler.Euler4 cases")
else {
  var t = new Date()
  for(var i in obj) {
    for(var k in obj[i]) {
      cases[k] = cases[k] || []
      for(var o in obj[i][k]) {
        cases[k].push(obj[i][k][o])
//        printobj(obj[i][k][o])
//  console.log(" ");
      }
    }
  }
  //console.log(JSON.stringify(cases,2,2))
  for (var i = 0; i < cases[""].length; i++) if (cases[""][i] != null) prove(cases[""][i], -1)
  for (var i in evidence) evidence["GND"] = cases["GND"]
  t = new Date() - t
//  print(JSON.stringify(evidence) + '\n')
//  print('//ENDS [' + step + ' steps/' + t + ' msec]')
}
