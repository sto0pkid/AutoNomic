// Euler proof mechanism -- Jos De Roo
version = '$Id: euler.js 1295 2007-05-11 16:52:51Z josd $'

/*
struct frame{
 rule_t	 	rule;
 int		src;
 int		ind;
 frame  	parent;
 env_t		env; //frames account for the processing of one body-item triple, but all the triples will effectively share an env
 ground_t	ground[];
}

struct rule_t{
 term	head
 term	body[];
}


//Associative array indexed by preds?
//maps preds to rules that 
struct evidence_t{
}

//Used to represent both triples and nodes. Nodes are represented by storing the node as the pred and having an empty args list.
struct term{
 ?? pred;
 ?? args;
}

typedef term var;
typedef term constant;
typedef term triple;


//Associative array indexed by vars?
struct env_t{

}

struct ground_t{
 rule_t src;
 env_t env;
}

GND...
*/

function prove(/* rule_t */ goal, maxNumberOfSteps) {
  var /* frame[] */ queue = [{rule:goal, src:0, ind:0, parent:null, env:{}, ground:[]}]
  if (typeof(evidence) == 'undefined') /* evidence_t */ evidence = {}
  if (typeof(step) == 'undefined') step = 0
  while (queue.length > 0) {
    var /* frame */ c = queue.pop()
    if (typeof(trace) != 'undefined') document.writeln('POP QUEUE\n' + JSON.stringify(c.rule) + '\n')
    var /* ground_t */ g = aCopy(c.ground)
    step++
    if (maxNumberOfSteps != -1 && step >= maxNumberOfSteps) return ''

    /* If this is either a fact or a rule where all the body-items have succeeded: */
    if (c.ind >= c.rule.body.length) {
      /* If this is the query: */
      if (c.parent == null) {
        for (var i = 0; i < c.rule.body.length; i++) {
          var /* term */ t = evaluate(c.rule.body[i], c.env)
          //why the per-pred evidence?
          if (typeof(evidence[t.pred]) == 'undefined') evidence[t.pred] = []
          //evidence for a particular fact is a rule where the head is the fact and the 
          //body consists of one item which is an n-tuple where the pred is GND and the args are ...
          evidence[t.pred].push({head:t, body:[{pred:'GND', args:c.ground}]})
        }
        continue
      }

      //why only if c.rule.body.length != 0 ?
      if (c.rule.body.length != 0) g.push({src:c.rule, env:c.env})
      var /*frame */ r = {rule:{head:c.parent.rule.head, body:c.parent.rule.body}, src:c.parent.src, ind:c.parent.ind, 
               parent:c.parent.parent != null ? new copy(c.parent.parent) : null, env:new copy(c.parent.env), ground:g}

      //constants found on the KB side from a fact/rule-head propagate back up to the body-item that called it
      //all this is really doing is making the constants found from this fact/rule-head available in the env for the next body-item in the parent
      unify(c.rule.head, c.env, r.rule.body[r.ind], r.env, true)

      //increment r.ind now because we will be processing the next body-item in the parent (or the completion of the parent).
      r.ind++

      //since we push it onto the end of the queue, continue, and then immediately pop, the next body-item of the
      //parent (or the completion of the parent) will be the next frame processed.
      queue.push(r)
      if (typeof(trace) != 'undefined') document.writeln('PUSH QUEUE\n' + JSON.stringify(r.rule) + '\n')
      continue
    }

    //current body-item to process
    var /* term */ t = c.rule.body[c.ind]

    /* What is builtin(t, c)?*/
    var b = builtin(t, c)
    if (b == 1) {
      g.push({src:{head:evaluate(t, c.env), body:[]}, env:{}})
      var /* frame */ r = {rule:{head:c.rule.head, body:c.rule.body}, src:c.src, ind:c.ind, parent:c.parent, env:c.env, ground:g}
      r.ind++
      queue.push(r)
      if (typeof(trace) != 'undefined') document.writeln('PUSH QUEUE\n' + JSON.stringify(r.rule) + '\n')
      continue
    }
    else if (b == 0) continue
    //if there are no rules that use the pred of the current body-item then just continue, there are no solutions for this body-item.
    if (cases[t.pred] == null) continue
    //src is redundant, it is equivalent to k.
    var src = 0
    //loop over all the rules that use the pred of the current body-item being processed:
    for (var k = 0; k < cases[t.pred].length; k++) {
      var /* rule_t */ rl = cases[t.pred][k]
      src++
      var /* ground_t */ g = aCopy(c.ground)
      //why do we push this to ground?
      if (rl.body.length == 0) g.push({src:rl, env:{}})
      /*
      {
       rule = k'th rule using t.pred in cases
       src = k
       ind = 0 // start at 1st body-item of this rule (index 0)
       parent = current frame
       env = {} ?
       ground = c.ground + {src:rl, env{}} ?
      }
      */
      var /* frame */ r = {rule:rl, src:src, ind:0, parent:c, env:{}, ground:g}
      //Constants from query-side propagate down into the rule being called
      if (unify(t, c.env, rl.head, r.env, true)) {
        var /* frame*/ ep = c  // euler path: too strict, cuts too many cases
        while (ep = ep.parent) if (ep.src == c.src && unify(ep.rule.head, ep.env, c.rule.head, c.env, false)) break
        if (ep == null) {
          //Place the frame onto the front of the stack. This causes the frames to go onto the queue in reverse order
	  //of how the rules are listed in the kb (how they're listed in 'cases' at least), but that's okay because
	  //we pop off the end of the queue so we end up processing them in the original order.
	  //**COMPLEXITY BUG** This is still not quite right though!
          queue.unshift(r)
          //Don't be confused by this message; if we make it here, we *don't* have an Euler path.
          if (typeof(trace) != 'undefined') document.writeln('EULER PATH UNSHIFT QUEUE\n' + JSON.stringify(r.rule) + '\n')
        }
      }
    }
  }
}


/*
term s		source?
env_t senv
term d	destination?
denv
f	place values into destination environment 
*/
function /* bool */ unify(/* term */ s,/* env_t */ senv,/* term */ d,/* env_t */ denv, /* bool */ f) {
  if (typeof(trace) != 'undefined') document.writeln('UNIFY\n' + JSON.stringify(s) + '\nWITH\n' + JSON.stringify(d) + '\n')
  if (isVar(s.pred)) {
    var /* term */ sval = evaluate(s, senv)
    //null in case s is an unground variable
    if (sval != null) return unify(sval, senv, d, denv, f)
    else return true
  }
  else if (isVar(d.pred)) {
    var /* term */ dval = evaluate(d, denv)
    //null in case d is an unground variable
    if (dval != null) return unify(s, senv, dval, denv, f)
    else {
      //*BUG* true != null && false != null, this will cause a bug during ep-check when variable binding is supposed to be disabled.
      if (f != null) denv[d.pred] = evaluate(s, senv)
      return true
    }
  }
  //unify constant with constant (if args.length == 0) or triple with triple (if args.length != 0)
  else if (s.pred == d.pred && s.args.length == d.args.length) {
    for (var i = 0; i < s.args.length; i++) if (!unify(s.args[i], senv, d.args[i], denv, f)) return false
    return true
  }
  else {
    if (typeof(trace) != 'undefined') document.writeln('FAILED TO UNIFY\n' + JSON.stringify(s) + '\nWITH\n' + JSON.stringify(d) + '\n')
    return false
  }
}


/*
If t is a triple representing an unground variable, return null.
If t is a triple representing a ground variable, return its constant binding.
If t is a triple representing a constant, return t.
If t is actually a triple, return the same triple but with its arguments evaluated.

This allows for evaluating arbitrarily nested triples btw.
*/

function /* term */ evaluate(/* term */ t, /* env_t */ env) {
  /*If the term represents a variable */
  if (isVar(t.pred)) {
    var /* term */ a = env[t.pred]
    //null in case 'a' is an unbound variable.
    if (a != null) return evaluate(a, env)
    else return null
  }


  /*If the term represents a constant */
  else if (t.args.length == 0) return t


  /*If the term represents a triple */
  else {
    var /* term[] */ n = []
    for (var i = 0; i < t.args.length; i++) {
      var /* term */ a = evaluate(t.args[i], env)
      if (a != null) n.push(a)
      else n.push({pred:t.args[i].pred, args:[]})
    }
    return {pred:t.pred, args:n}
  }
}

function isVar(s) { return s.charAt(0) == '?' }
function aCopy(t) { var a = new Array(); for (var i = 0; i < t.length; i++) a[i] = t[i]; return a }
/*how the hell does this work?*/
function copy(t) { for (var i in t) theis[i] = t[i] }
