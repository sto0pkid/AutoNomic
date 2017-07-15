// Euler proof mechanism -- Jos De Roo
version = '$Id: euler.js,v 1.35 2006/12/17 01:25:01 josd Exp $'

function prove(goal, maxNumberOfSteps) {
  var queue = [{rule:goal, src:0, ind:0, parent:null, env:{}, ground:[]}]
  if (typeof(evidence) == 'undefined') evidence = {}
  if (typeof(step) == 'undefined') step = 0
  while (queue.length > 0) {
    var c = queue.pop()
    if (typeof(trace) != 'undefined') document.writeln('POP QUEUE\n' + JSON.stringify(c.rule) + '\n')
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
      if (typeof(trace) != 'undefined') document.writeln('PUSH QUEUE\n' + JSON.stringify(r.rule) + '\n')
      continue
    }
    var t = c.rule.body[c.ind]
    var b = builtin(t, c)
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
    for (var k = 0; k < cases[t.pred].length; k++) {
      var rl = cases[t.pred][k]
      src++
      var g = aCopy(c.ground)
      if (rl.body.length == 0) g.push({src:rl, env:{}})
      var r = {rule:rl, src:src, ind:0, parent:c, env:{}, ground:g}
      if (unify(t, c.env, rl.head, r.env, true)) {
        var ep = r  // euler path
        while (ep = ep.parent) if (ep.src == r.src && unify(ep.rule.head, ep.env, r.rule.head, r.env, false)) break
        if (ep == null) {
          queue.unshift(r)
          if (typeof(trace) != 'undefined') document.writeln('EULER PATH UNSHIFT QUEUE\n' + JSON.stringify(r.rule) + '\n')
        }
      }
    }
  }
}

function unify(s, senv, d, denv, f) {
  if (typeof(trace) != 'undefined') document.writeln('UNIFY\n' + JSON.stringify(s) + '\nWITH\n' + JSON.stringify(d) + '\n')
  if (isVar(s.pred)) {
    var sval = evaluate(s, senv)
    if (sval != null) return unify(sval, senv, d, denv, f)
    else return true
  }
  else if (isVar(d.pred)) {
    var dval = evaluate(d, denv)
    if (dval != null) return unify(s, senv, dval, denv, f)
    else {
      if (f != false) denv[d.pred] = evaluate(s, senv)
      return true
    }
  }
  else if (s.pred == d.pred && s.args.length == d.args.length) {
    for (var i = 0; i < s.args.length; i++) if (!unify(s.args[i], senv, d.args[i], denv, f)) return false
    return true
  }
  else {
    if (typeof(trace) != 'undefined') document.writeln('FAILED TO UNIFY\n' + JSON.stringify(s) + '\nWITH\n' + JSON.stringify(d) + '\n')
    return false
  }
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
