/**
 *
 * Rules:
 * - unused variables/methods are kept there
 * - if a replace generates an error the transformation will be ignore and then
 *   process will continue
 *
 */
import parser from "@babel/parser";
import traverse from "@babel/traverse";
import t from "@babel/types";
import generate from "@babel/generator";
import beautify from "js-beautify";
import { readFileSync } from "fs";
import { exit } from "process";
import vm from 'node:vm';
import jQuery from "jquery";
import fs from 'fs';
import path from "path";
import browserEnv from "browser-env";
browserEnv();
const jquery = jQuery(globalThis.window);
let eval_map = {};
let new_file_path;
let js_context = vm.createContext(globalThis)
js_context.jQuery = jquery;

const VERBOSE = true;

function log(...args) {
  console.log(...args);
}

function error(...args) {
  if (VERBOSE)
    console.log(...args);
}

function isASCII(str) {
  return str && typeof str == "string" && (/^[\x00-\x7F]*$/).test(str);
}

function isValidVariableName(str) {
  return str && (/^[a-zA-Z_$][\w$]*$/).test(str);
}

function tryReplaceWith(r, _with) {
  try {
    r.replaceWith(_with);
  } catch {
    try {
      //r.scope.crawl();
      r.replaceWith(_with);
    } catch (e) {
      error(e);
      log(e.toString());
      exit(1);
    }
  }
}

// sequence expression to multiple statements
function getNamesFromSequenceExpression(path) {
  let names = []
  const expr = path.expressions.concat().reverse();
  for (const v of expr) {
    if (t.isAssignmentExpression(v)) {
      names.push(v.left.name);
    }
  }
  return names;
  path.replaceWithMultiple(path.expressions);
}

function findParamIdx(name, params) {
  for (let i = 0; i < params.length; i++) {
    if (params[i].name == name)
      return i;
  }
  return -1;
  //throw `param idx ${name} not found`;
}

function substituteArguments(path, params, actuals) {
  if (t.isLiteral(path))
    return path;
  if (t.isBreakStatement(path))
    return path;
  if (t.isIdentifier(path)) {
    const idx = findParamIdx(path.name, params);
    if (idx == -1)
      return path;
    if (idx >= actuals.length)
      throw `argument ${path.name} not found`;
    return actuals[idx];
  }

  if (t.isExpressionStatement(path)) {
    const new_exp = substituteArguments(path.expression, params, actuals);
    const new_exp_s = t.expressionStatement(new_exp);
    return new_exp_s;
  }
  if (t.isBinaryExpression(path)) {
    const new_left = substituteArguments(path.left, params, actuals);
    const new_right = substituteArguments(path.right, params, actuals);
    const new_expr = t.binaryExpression(path.operator, new_left, new_right);
    return new_expr;
  }
  if (t.isUnaryExpression(path)) {
    const new_arg = substituteArguments(path.argument, params, actuals);
    const new_expr = t.unaryExpression(path.operator, new_arg);
    return new_expr;
  }
  if (t.isMemberExpression(path)) {
    const new_obj = substituteArguments(path.object, params, actuals);
    const new_prop = substituteArguments(path.property, params, actuals);
    const new_expr = t.memberExpression(new_obj, new_prop, path.computed);
    return new_expr;
  }
  if (t.isCallExpression(path)) {
    const new_args = path.arguments.map(a => substituteArguments(a, params, actuals));
    const new_callee = substituteArguments(path.callee, params, actuals);
    const new_expr = t.callExpression(new_callee, new_args);
    return new_expr;
  }
  if (t.isAssignmentExpression(path)) {
    const new_right = substituteArguments(path.right, params, actuals);
    const new_expr = t.assignmentExpression(path.operator, path.left, new_right);
    return new_expr;
  }
  if (t.isSequenceExpression(path)) {
    const new_expr = path.expressions.map(e => substituteArguments(e, params, actuals));
    const new_seq = t.sequenceExpression(new_expr);
    return new_seq;
  }
  if (t.isForStatement(path)) {
    const init = path.init;
    const new_test = path.test ? substituteArguments(path.test, params, actuals) : null;
    const new_update = path.update ? substituteArguments(path.update, params, actuals) : null;
    const new_body = substituteArguments(path.body, params, actuals);
    const new_for = t.forStatement(init, new_test, new_update, new_body);
    return new_for;
  }
  if (t.isTryStatement(path)) {
    const new_block = substituteArguments(path.block, params, actuals);
    const new_handler = substituteArguments(path.handler, params, actuals);
    const new_try = t.tryStatement(new_block, new_handler);
    return new_try;
  }
  if (t.isBlockStatement(path)) {
    const new_body = path.body.map(a => substituteArguments(a, params, actuals));
    const new_block = t.blockStatement(new_body);
    return new_block;
  }
  if (t.isCatchClause(path)) {
    const new_body = substituteArguments(path.body, params, actuals);
    const new_catch = t.catchClause(path.param, new_body);
    return new_catch;
  }
  if (t.isIfStatement(path)) {
    const new_test = substituteArguments(path.test, params, actuals);
    const new_cons = substituteArguments(path.consequent, params, actuals);
    const new_altern = path.alternate ? substituteArguments(path.alternate, params, actuals) : null;
    const new_if = t.ifStatement(new_test, new_cons, new_altern);
    return new_if;
  }
  if (t.isUpdateExpression(path)) {
    const new_arg = substituteArguments(path.argument, params, actuals);
    const new_upd = t.updateExpression(path.operator, new_arg, path.prefix);
    return new_upd;
  }
  if (t.isLogicalExpression(path)) {
    const new_left = substituteArguments(path.left, params, actuals);
    const new_right = substituteArguments(path.right, params, actuals);
    const new_log = t.logicalExpression(path.operator, new_left, new_right);
    return new_log;
  }
  if (t.isConditionalExpression(path)) {
    const new_test = substituteArguments(path.test, params, actuals);
    const new_cons = substituteArguments(path.consequent, params, actuals);
    const new_altern = substituteArguments(path.alternate, params, actuals);
    const new_if = t.conditionalExpression(new_test, new_cons, new_altern);
    return new_if;
  }
  if (t.isVariableDeclaration(path)) {
    const new_decs = path.declarations.map(d => substituteArguments(d, params, actuals));
    const new_dec = t.variableDeclaration(path.kind, new_decs);
    return new_dec;
  }
  if (t.isVariableDeclarator(path)) {
    const new_init = path.init ? substituteArguments(path.init, params, actuals) : null;
    const new_dec = t.variableDeclarator(path.id, new_init);
    return new_dec;
  }
  if (t.isSwitchStatement(path)) {
    const new_disc = substituteArguments(path.discriminant, params, actuals);
    const new_cases = path.cases.map(c => substituteArguments(c, params, actuals));
    const new_swi = t.switchStatement(new_disc, new_cases);
    return new_swi;
  }
  if (t.isSwitchCase(path)) {
    const new_test = path.test ? substituteArguments(path.test, params, actuals) : null;
    const new_cons = path.consequent.map(c => substituteArguments(c, params, actuals));
    const new_swi = t.switchCase(new_test, new_cons);
    return new_swi;
  }
  if (t.isReturnStatement(path)) {
    const new_arg = path.argument ? substituteArguments(path.argument, params, actuals) : null;
    const new_ret = t.returnStatement(new_arg);
    return new_ret;
  }
  if (t.isObjectExpression(path)) {
    // too risky
    return path;
  }

  return path;
  throw `argument ${path.type} not found`;
}

function handleStringLiteral(path) {
  //console.log(path.node.value);
  // so the idea here is to solve this problem
  // ```
  //   func(....) + 'a' + 'b'
  // ```
  // in this case normal deobfuscators have difficulties since the first
  // left part cannot be safely resolved and therefore stop deobfuscating
  // but 'a' + 'b' can be simplified
  if (path?.parent?.type == 'BinaryExpression') {
    if (path.key == 'right') {
      if (t.isStringLiteral(path?.parent?.left?.right)) {
        if (path.parent.operator == '+') {
          const new_string = path.parent.left.right.value + path.node.value;
          const new_node = t.binaryExpression('+', path.parent.left.left, t.stringLiteral(new_string));
          path.parentPath.replaceWith(new_node);
        }
      }
    } else if (path.key == 'left') {
      //console.log(path.parent.right);
    }
  }
}
function handleNumericLiteral(path) {
  //console.log(path.node.value);
  // so the idea here is to solve this problem
  // ```
  //   func(....) + 2 + 4
  // ```
  // in this case normal deobfuscators have difficulties since the first
  // left part cannot be safely resolved and therefore stop deobfuscating
  // but 2 + 4 can be simplified
  if (path?.parent?.type == 'BinaryExpression') {
    if (path.key == 'right') {
      if (t.isNumericLiteral(path?.parent?.left?.right)) {
        let new_value = 0;
        switch (path.parent.operator) {
          case '+':
            new_value = path.parent.left.right.value + path.node.value;
            break;
          case '-':
            new_value = path.parent.left.right.value - path.node.value;
            break;
          case '*':
            new_value = path.parent.left.right.value * path.node.value;
            break;

          default:
            return;
        }
        const new_node = t.binaryExpression(path.parent.operator, path.parent.left.left, t.numericLiteral(new_value));
        path.parentPath.replaceWith(new_node);
      }
    } else if (path.key == 'left') {
      //console.log(path.parent.right);
    }
  }
}

function handleCallExpression(path) {
  const params = path.node.arguments;
  let all_literals = !params.map(p => (t.isLiteral(p))).includes(false);
  if (t.isIdentifier(path.node.callee) && all_literals) {
    const code = generate.default(path.node).code
    if (eval_map[code]) {
      path.replaceWith(eval_map[code]);
      return;
    }
    //let par = path;
    //let tot = 0;
    //while (par.parentPath && tot < 1) {
    //const parent = generate.default(par.node).code
    //const decl = varDecl(parent);
    try {
      let tmp_ctx = vm.createContext(js_context);
      //vm.runInContext(decl, tmp_ctx);
      const value = vm.runInContext(code, tmp_ctx);
      if (isASCII(value)) {
        tryReplaceWith(path, t.stringLiteral(value));
        eval_map[code] = t.stringLiteral(value);
        return;
      }
    } catch (e) {
      //error(e);
    }
    //  par = par.parentPath;
    //  tot++;
    //}
  }
}

function handleObjectProperty(path) {
  const parent = path.parentPath.parent;
  const scope = path.parentPath.parentPath.scope;

  let objName = undefined;
  if (t.isAssignmentExpression(parent) && t.isIdentifier(parent.left)) {
    objName = parent.left.name;
  } else {
    objName = path.parentPath?.parent?.id?.name;
  }
  if (objName == undefined)
    return;
  if (t.isFunctionExpression(path.node.value)) {

    const is_constant = scope.bindings[objName]?.constant || scope.bindings[objName]?.constantViolations.length == 1;
    const body = path.node.value.body.body;
    const params = path.node.value.params;
    if (!t.isReturnStatement(body[0]))
      return;

    if (scope.bindings[objName] && is_constant) {
      const refs = scope.bindings[objName].referencePaths;
      for (const r of refs) {
        if (r.parent?.property?.name && r.parent?.property?.name == path?.node?.key?.name) {
          //log(r.parent.property)
          //log(path.node.key);
          //log("----------------------------------------------------");
          if (t.isMemberExpression(r.parent) && t.isCallExpression(r.parentPath.parent)) {
            //if (t.isCallExpression(r.parentPath.parent) && path.node.value.params.length == r.parentPath.parent.arguments.length) {
            // RETURN
            // BINARY EXPRESSION
            if (t.isBinaryExpression(body[0].argument)) {
              const new_expr = substituteArguments(body[0].argument, params, r.parentPath.parent.arguments);
              //if (body[0].argument.left.name == path.node.value.params[0].name) {
              //  new_expr = t.parenthesizedExpression(t.binaryExpression(body[0].argument.operator, t.parenthesizedExpression(r.parentPath.parent.arguments[0]), t.parenthesizedExpression(r.parentPath.parent.arguments[1])));
              //} else {
              //  new_expr = t.parenthesizedExpression(t.binaryExpression(body[0].argument.operator, r.parentPath.parent.arguments[1], r.parentPath.parent.arguments[0]));
              //}
              r.parentPath.parentPath.scope.crawl();
              tryReplaceWith(r.parentPath.parentPath, new_expr);
            }
            // CALL EXPRESSION
            else if (t.isCallExpression(body[0].argument)) {
              const arg = body[0].argument;
              const new_call = substituteArguments(arg, params, r.parentPath.parent.arguments);
              r.parentPath.parentPath.scope.crawl();
              tryReplaceWith(r.parentPath.parentPath, new_call);
            }
          }
        }
      }
    }
  } else if (t.isLiteral(path.node.value)) {

    const is_constant = path.parentPath.scope.bindings[objName]?.constant;

    if (path.parentPath.scope.bindings[objName] && is_constant) {
      const refs = path.parentPath.scope.bindings[objName].referencePaths;
      for (const r of refs) {
        // cause we are coming from object property so we access through member expression
        if (t.isMemberExpression(r.parent) && !t.isAssignmentExpression(r.parentPath.parent) && r.parent.property.name == path.node.key.name) {
          r.parentPath.scope.crawl();
          tryReplaceWith(r.parentPath, path.node.value);
        }
      }
    }
  }
}


function handleFunctionDeclarationCallExpression(path) {
  const { node } = path;
  const { id, body, params } = node;
  if (!t.isReturnStatement(body.body[0])) return;
  const proxyExpression = body.body[0].argument;
  if (!t.isCallExpression(proxyExpression))
    return;

  const { constant, referencePaths } = path.parentPath.scope.getBinding(id.name);
  if (!constant) return;

  for (let rp of referencePaths) {
    let { parent } = rp;
    if (
      !t.isCallExpression(parent) ||
      (t.isCallExpression(parent) &&
        parent.callee.name !== rp.node.name)
    )
      continue;

    const new_callee = substituteArguments(proxyExpression.callee, params, rp.parent.arguments);
    let new_args = []
    for (const ar of proxyExpression.arguments) {
      const new_arg = substituteArguments(ar, params, rp.parent.arguments);
      if (new_arg) {
        new_args.push(new_arg);
      } else {
        exit(1);
      }
    }

    const new_call = t.callExpression(new_callee, new_args);
    tryReplaceWith(rp.parentPath, new_call);

  }
}

function handleFunctionDeclaration(path) {
  const { node } = path;
  const { id, body, params } = node;
  if (!t.isReturnStatement(body.body[0])) return;
  const proxyExpression = body.body[0].argument;
  if (t.isCallExpression(proxyExpression)) {
    handleFunctionDeclarationCallExpression(path);
    return;
  }

  if (
    !t.isBinaryExpression(proxyExpression) &&
    !t.isUnaryExpression(proxyExpression)
  )
    return;
  const { constant, referencePaths } = path.parentPath.scope.getBinding(id.name);
  if (!constant) return;

  for (let rp of referencePaths) {
    let { parentPath } = rp;
    if (
      !t.isCallExpression(parent) ||
      (t.isCallExpression(parent) &&
        parent.callee !== rp.node)
    )
      continue;
    const proxyExpressionCopyAst = parser.parse(
      generate.default(proxyExpression).code
    );

    const replaceVarsInExpressionWithArguments = {
      Identifier(_path) {
        for (let i = 0; i < params.length; i++) {
          if (params[i].name == _path.node.name && t.isIdentifier(parentPath.node.arguments[i])) {
            _path.replaceWith(t.parenthesizedExpression(parentPath.node.arguments[i]));
            return;
          }
        }
      },
    };

    traverse.default(proxyExpressionCopyAst, replaceVarsInExpressionWithArguments);
    parent.replaceInline(proxyExpressionCopyAst.program.body);
  }
}
function handleUnaryExpression(path) {
  let { confident, value } = path.evaluate();
  if (!confident) return;

  if (typeof value == "string") {
    path.replaceWith(t.stringLiteral(value));
    return;
  }
  if (typeof value == "number") {
    path.replaceWith(t.numericLiteral(value));
    return;
  }
  if (typeof value == "boolean") {
    path.replaceWith(t.booleanLiteral(value));
    return;
  }
}

function handleBinaryExpression(path) {
  // "" + f --> f
  if (path.node.operator == '+') {
    if (path.node.left?.value == '') {
      path.replaceWith(path.node.right);
    } else if (path.node.right?.value == '') {
      path.replaceWith(path.node.left);
    }
  }

  let { confident, value } = path.evaluate();
  if (!confident) return;

  if (typeof value == "string") {
    path.replaceWith(t.stringLiteral(value));
    return;
  }
  if (typeof value == "number") {
    path.replaceWith(t.numericLiteral(value));
    return;
  }
  if (typeof value == "boolean") {
    path.replaceWith(t.booleanLiteral(value));
    return;
  }
}

function handleAssignmentExpression(path) {
  if (path.node.operator == '=' && t.isIdentifier(path.node.left) && (t.isIdentifier(path.node.right) || t.isLiteral(path.node.right))) {
    const name = path.node.left.name;
    if (path.scope.bindings[name]) {
      const is_constant = path.scope.bindings[name]?.constant || path.scope.bindings[name]?.constantViolations.length == 1;
      if (!is_constant)
        return;
      const refs = path.scope.bindings[name].referencePaths.concat().reverse();
      for (const r of refs) {
        if (r.node.name != name)
          continue;
        if (path.scope.bindings[name]?.constant && path.node.right) {
          tryReplaceWith(r, path.node.right);
        } else {
          if (r.node.end < path.scope.bindings[name].constantViolations[0].node.end && path.node.right) {
            tryReplaceWith(r, path.node.right);
          } else if (path.scope.bindings[name].constantViolations[0].node.right) {
            tryReplaceWith(r, path.scope.bindings[name].constantViolations[0].node.right);
          }
        }
      }
    }
  }
}

function handleForStatement(path) {
  return;
  if (t.isVariableDeclaration(path.node.init)) {
    let var_names = [];
    let var_ids = [];
    if (path.scope.bindings) {
      const ex_code = generate.default(path.node).code
      log(ex_code);
      log(path.scope.bindings);

      const visitor = {
        VariableDeclarator(path) {
          handleVariableDeclarator(path);
        },
        CallExpression(path) {
          log(Object.keys(path.scope.bindings));
        },
        MemberExpression(path) {
          log(Object.keys(path.scope.bindings));
        }
      };

      try {
        let ast = parser.parse(ex_code);
        traverse.default(ast, visitor);
        let deobfCode = generate.default(ast, { comments: false }).code;
        log(deobfCode);

      } catch (e) {
        error(e);
      }
      exit(1);
    }
    return;
    for (const d of path.node.init.declarations) {
      if (t.isIdentifier(d.init)) {
        var_names.push(d.id);
        var_ids.push(d.init);
      }
    }

    const new_for = substituteArguments(path.node, var_names, var_ids);
    const code = generate.default(new_for).code
    const ex_code = generate.default(path.node).code

    //if (code != ex_code) {
    //  path.replaceWith(new_for);
    //}
  }
}

function handleVariableDeclarator(path) {
  const name = path?.node?.id?.name;
  if (!name)
    return;

  const is_constant = path.scope.bindings[name]?.constant || path.scope.bindings[name]?.constantViolations.length == 1;
  if (path?.node?.init && (t.isStringLiteral(path.node.init) || t.isIdentifier(path.node.init) || t.isRegExpLiteral(path.node.init))) {
    if (is_constant) {
      const refs = path.scope.bindings[name]?.referencePaths;
      for (const r of refs) {
        if (t.isUpdateExpression(r.parent))
          continue;
        if (r.node.name != name)
          continue;
        if (path.scope.bindings[name]?.constant) {
          tryReplaceWith(r, path.node.init);
        } else {
          if (r.node.end < path.scope.bindings[name].constantViolations[0].node.end) {
            tryReplaceWith(r, path.node.init);
          } else if (path.scope.bindings[name].constantViolations[0].node.init) {
            tryReplaceWith(r, path.scope.bindings[name].constantViolations[0].node.init);
          }
        }
      }
      return;
    }
  }

  if (path?.node?.init && t.isNumericLiteral(path.node.init) && path.scope.bindings[name] && is_constant) {
    const refs = path.scope.bindings[name].referencePaths.concat().reverse();
    for (const r of refs) {
      if (t.isUpdateExpression(r.parent))
        continue;
      if (r.node.name != path.node?.id?.name)
        continue;
      if (path.scope.bindings[name]?.constant) {
        //const assign = t.assignmentExpression('=', r.node, t.isIdentifier(path.node.right));
        tryReplaceWith(r, path.node.init);
      } else {
        if (r.node.end < path.scope.bindings[name].constantViolations[0].node.end) {
          tryReplaceWith(r, path.node.init);
        } else if (path.scope.bindings[name].constantViolations[0].node.init) {
          tryReplaceWith(r, path.scope.bindings[name].constantViolations[0].node.init);
        }
      }
    }
  }
}

function handleMemberExpression(path) {
  //const s = source.slice(path.node.start, path.node.end).toString();
  // some something like "ciao"["indexOf"] -> "ciao".indexOf()
  //const code = generate.default(path.parent).code
  // TODO: risky ... maybe better check object
  if (/*(t.isStringLiteral(path.node.object) || t.isIdentifier(path.node.object)) &&*/ t.isStringLiteral(path.node.property) && isValidVariableName(path.node.property.value)) {
    const prop_id = t.identifier(path.node.property.value);
    if (t.isCallExpression(path.parent) && path.parent.callee == path.node) {
      const new_expr = t.memberExpression(path.node.object, prop_id);
      let params = path.parent.arguments;
      let new_call = t.callExpression(new_expr, params);
      tryReplaceWith(path.parentPath, new_call);

      return;
    }

    //const new_prop = t.parenthesizedExpression(t.memberExpression(path.node.object, prop_id));
    const new_prop = t.memberExpression(path.node.object, prop_id);
    tryReplaceWith(path, new_prop);

  }

  if (t.isSequenceExpression(path.node.property)) {
    const last = path.node.property.expressions[path.node.property.expressions.length - 1];

    if (
      t.isStringLiteral(path.node.property.expressions[path.node.property.expressions.length - 1]) &&
      isValidVariableName(path.node.property.expressions[path.node.property.expressions.length - 1].value)) {
      const code = generate.default(path.node).code
      //log(code);
      const prop_id = t.identifier(last.value);
      if (t.isCallExpression(path.parent) && path.parent.callee == path.node) {
        const new_expr = t.memberExpression(path.node.object, prop_id);
        let params = path.parent.arguments;
        let new_call = t.callExpression(new_expr, params);
        tryReplaceWith(path.parentPath, new_call);

        return;
      }

      //const new_prop = t.parenthesizedExpression(t.memberExpression(path.node.object, prop_id));
      const new_prop = t.memberExpression(path.node.object, prop_id);
      tryReplaceWith(path, new_prop);
    } else {
      // try to resolve the sequence inside like:
      //   L[(W = "qUur", o = 728, _0x2d88(o - -548 - 478 - -545, W))]

      try {
        const names = getNamesFromSequenceExpression(path.node.property, path)
        let names_init = "";
        for (const n of names) {
          names_init += `var ${n};`
        }
        const code = names_init + generate.default(path.node.property).code;
        let tmp_ctx = vm.createContext(js_context);
        const value = vm.runInContext(code, tmp_ctx);
        if (isASCII(value)) {
          const new_memb = t.memberExpression(path.node.object, t.stringLiteral(value), true)
          tryReplaceWith(path, new_memb);
        }
      } catch (e) {
        //log(e.toString())
        //exit(1);
      }
    }
  }
}

function handleIfStatement(path) {
  if (t.isBooleanLiteral(path.node.test)) {
    if (path.node.test.value == false) {
      if (path.node.alternate) {
        tryReplaceWith(path, path.node.alternate);
      } else {
        path.remove();
      }
    } else {
      tryReplaceWith(path, path.node.consequent);
    }
  }
}

const step1Visitor = {
  MemberExpression(path) {
    handleMemberExpression(path);
  },
  ForStatement(path) {
    handleForStatement(path);
  },
  StringLiteral(path) {
    handleStringLiteral(path);
  },
  NumericLiteral(path) {
    handleNumericLiteral(path);
  },
  IfStatement(path) {
    handleIfStatement(path);
  },
  VariableDeclarator(path) {
    handleVariableDeclarator(path);
  },
  FunctionDeclaration(path) {
    handleFunctionDeclaration(path);
  },
  AssignmentExpression(path) {
    handleAssignmentExpression(path);
  },
  ObjectProperty(path) {
    handleObjectProperty(path);
  },
  BinaryExpression(path) {
    handleBinaryExpression(path);
  },
  UnaryExpression(path) {
    handleUnaryExpression(path);
  }
};

const step2Visitor = {
  BinaryExpression(path) {
    handleBinaryExpression(path);
  },
  ForStatement(path) {
    handleForStatement(path);
  },
  UnaryExpression(path) {
    handleUnaryExpression(path);
  },
  StringLiteral(path) {
    handleStringLiteral(path);
  },
  NumericLiteral(path) {
    handleNumericLiteral(path);
  },
  IfStatement(path) {
    handleIfStatement(path);
  },
  VariableDeclarator(path) {
    handleVariableDeclarator(path);
  },
  MemberExpression(path) {
    handleMemberExpression(path);
  },
  FunctionDeclaration(path) {
    handleFunctionDeclaration(path);
  },
  AssignmentExpression(path) {
    handleAssignmentExpression(path);
  },
  CallExpression(path) {
    handleCallExpression(path);
  },
  ObjectProperty(path) {
    handleObjectProperty(path);
  }
};

const step3Visitor = {
  BinaryExpression(path) {
    handleBinaryExpression(path);
  },
  ForStatement(path) {
    handleForStatement(path);
  },
  UnaryExpression(path) {
    handleUnaryExpression(path);
  },
  StringLiteral(path) {
    handleStringLiteral(path);
  },
  NumericLiteral(path) {
    handleNumericLiteral(path);
  },
  IfStatement(path) {
    handleIfStatement(path);
  },
  VariableDeclarator(path) {
    handleVariableDeclarator(path);
  },
  MemberExpression(path) {
    handleMemberExpression(path);
  },
  FunctionDeclaration(path) {
    handleFunctionDeclaration(path);
  },
  AssignmentExpression(path) {
    handleAssignmentExpression(path);
  },
  ObjectProperty(path) {
    handleObjectProperty(path);
  }
};

const unusedVisitor = {
  IfStatement(path) {
    handleIfStatement(path);
  },
  StringLiteral(path) {
    handleStringLiteral(path);
  },
  VariableDeclarator(path) {
    const name = path.node.id.name;
    const bind = path.parentPath.scope.getBinding(name);
    if (!bind) {
      try {
        path.remove();
      } catch {
      }
      return;
    }
    if (bind.referencePaths.length == 0) {
      try {
        path.remove();
      } catch {
      }
      return;
    }
  },
  FunctionDeclaration(path) {
    const name = path.node.id.name;
    const bind = path.parentPath.scope.getBinding(name);
    if (!bind) {
      try {
        path.remove();
      } catch {
      }
      return;
    }
    if (bind.referencePaths.length == 0) {
      try {
        path.remove();
      } catch {
      }
      return;
    }
  },
};

function step(stepN, source, visitor, times) {
  for (let i = 0; i < times; i++) {

    try {
      let ast = parser.parse(source);
      traverse.default(ast, visitor);
      let deobfCode = generate.default(ast, { comments: false }).code;
      deobfCode = beautify(deobfCode, {
        indent_size: 2,
        space_in_empty_paren: true,
      });

      source = deobfCode;
      if (source != "")
        writeCodeToFile(source);
      console.log(`[-] step ${stepN} -> ${i + 1}/${times} traverse completed!`);
    } catch (e) {
      error(e);
      break;
    }
  }

  log(`[-] step ${stepN} completed`);

  return source;
}

function writeCodeToFile(code) {
  fs.writeFileSync(new_file_path, code);
}

async function run() {
  let ctx = { ...globalThis };
  ctx.jQuery = jquery;
  let jsContext = vm.createContext(globalThis)
  let code = (readFileSync("./embed.js", "utf8"));
  try {
    let value = await vm.runInContext(code, jsContext);
    log("value", value);
  } catch (e) {
    log(e);
  }
  exit(1);
}

function main() {
  if (!process.argv[2] || process.argv[2] == "") {
    console.log(`[x] Insert a file plzzzz`);
    return;
  }
  const file_path = path.join("./", process.argv[2]);
  if (!fs.existsSync(file_path)) {
    console.log(`[x] Insert a VALID file plzzzz`);
    return;
  }
  const dir_path = "./output";
  if (!fs.existsSync(dir_path)) {
    fs.mkdirSync(dir_path);
  }
  let parts = file_path.split("/").at(-1).split(".");
  parts.pop();
  const name = parts.join(".") + ".deob.js";
  new_file_path = path.join(dir_path, name);

  let source = readFileSync(file_path, "utf8");
  try {
    // add to scope globally defined functions
    vm.runInContext(source, js_context);
  } catch (e) {
  }
  source = step(1, source, step1Visitor, 1);
  source = step(2, source, step2Visitor, 3);
  source = step(3, source, step3Visitor, 1);
  // optional .... more readable ... could lose accuracy tho
  source = step(4, source, unusedVisitor, 1);

  writeCodeToFile(source);
  console.log(`\n[-] File saved in ${new_file_path}`);
  exit(0);
}

main();
