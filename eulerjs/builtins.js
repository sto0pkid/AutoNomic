// Euler proof mechanism -- Jos De Roo
// $Id: builtins.js 1295 2007-05-11 16:52:51Z josd $

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
