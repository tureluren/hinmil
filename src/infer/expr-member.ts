// ============================================================================
// Member-expression inference: property access on unions, TypeReps, TCons,
// TVars, computed access, builtin constructors (extracted from expressions.ts)
//
// Plain language: this file answers "what is the type of `obj.something`?".
// That depends entirely on what `obj` is — a record with named fields, an
// array (with built-in methods like map), a class instance, a sum type
// variant, a union of several possibilities, …  Each of those cases has its
// own lookup path here; if none of them knows the property, a diagnostic
// ("unknown property") is produced.
// ============================================================================

import type * as estree from '../estree';
import { isAppliedObject, tOpenRecord, tRow } from '../hm/types';
import {
  Type,
  tVar,
  tCon,
  tFun,
  tNumber,
  tString,
  tBool,
  tUndefined,
  tVoid,
  tArray,
  tTuple,
  tUnion,
  tSpread,
  tAnyType,
  isAnyType,
  isWildcard,
  isSkolem,
  typeToString,
  prettyTypeToString,
  schemeToString,
  parseKvName,
  constraintBaseName,
  getReturnType,
  AstNode,
  T_UNION,
  T_ARRAY,
  T_ERROR,
  T_TYPEREP,
  T_MERGE,
  T_PICKED,
  T_SPREAD_ARRAY,
  isUnion,
} from '../hm/types';
import { TypeEnv, instantiate, generalize } from '../hm/env';
import { unify, UnificationError } from '../hm/unify';
import { TypeAnnotation} from '../commentParser';
import { lookupMethod, findMethodCandidates, getTypeArity, getMethodNames, MethodEntry, isMethodPrivate, isBuiltinType, isContainerIdentityMethod, hasAnyFallbackMethods } from '../registries/methodRegistry';
import { lookupConstraint, getEffectiveMethods } from '../registries/constraintRegistry';
import { getParentTypeName, isDataType, getDataType, getVariantRecordFields } from '../registries/dataTypeRegistry';
import {
  freshenType,
  structuralEquals,
  mapType,
} from '../hm/typeUtils';
import {
  narrowSumtypePropertyUnion,
  nonNullMemberKey,
  removeNullUndefined,
} from './narrowing';
import { freshVars} from './helpers';
import { someType } from '../hm/typeUtils';
import {
  resolveKvConstraintNames,
  collectAllKvConstraintNames,
  lookupConstraintMethod,
  lookupConstraintMethodOnTVar,
  lookupConstraintInstanceMethodOnTVar,
} from './expr-constraint-lookup';

import type { InferenceEngine } from './index';
import { inferExpression } from './expressions';

export function inferMemberExpression(engine: InferenceEngine, node: estree.MemberExpression, env: TypeEnv): Type {
  const type = inferMemberExpressionRaw(engine, node, env);
  // A branch narrowed by `obj.prop == null` on a non-record object marks the
  // path as non-null (see `narrowing.ts`, member null check).
  if (!node.computed && node.object?.type === 'Identifier' && node.property?.type === 'Identifier'
      && env.lookup(nonNullMemberKey(node.object.name, node.property.name))) {
    return removeNullUndefined(engine.subst.apply(type));
  }
  return type;
}

function inferMemberExpressionRaw(engine: InferenceEngine, node: estree.MemberExpression, env: TypeEnv): Type {
  const objectType = inferExpression(engine, node.object, env);
  let resolved = engine.subst.apply(objectType);

  // Expand type aliases (e.g., TCon('Person') from recursive type references)
  // so that record field access and method lookup work on the expanded type.
  resolved = engine.maybeExpandAlias(resolved);

  // --- A member of `Any` is `Any` (`json.data` after `JSON.parse` typed as
  //     `Any`): a fresh variable would pin on first use and leave a later
  //     `Object.assign ({}, json.data, x)` with an unresolvable operand.
  if (isAnyType(resolved)) {
    engine.recordNodeType(node.property, tAnyType);
    return tAnyType;
  }

  // --- Computed access: arr[i] => element type ---
  if (node.computed) {
    return inferComputedAccess(engine, node, env, objectType, resolved);
  }

  // --- Property access: obj.prop  or  obj.#privateField ---
  // PrivateIdentifier nodes also expose `.name` (without the leading '#').
  const propIsPrivate = node.property?.type === 'PrivateIdentifier';
  const propName = (node.property as estree.Identifier | estree.PrivateIdentifier).name;
  if (!propName) return tVar();
  // Private fields/methods (`obj.#x`, `this.#m()`) are class-scoped and not
  // tracked in the public method/property registries.  If we know the
  // receiver's class and have stashed the private member's type during
  // class inference (via a `Class##name :: T` annotation or initialiser),
  // return that type so hover / completion work inside the class body.
  // Otherwise return a fresh TVar to suppress "property does not exist".
  if (propIsPrivate) {
    let privType: Type = tVar();
    if (resolved.tag === 'TCon') {
      const stored = engine.privateClassMembers.get(`${resolved.name}##${propName}`);
      if (stored) privType = instantiate(generalize(env, stored));
    }
    engine.recordNodeType(node.property, privType);
    return privType;
  }

  // Record field access (structural)
  if (resolved.tag === 'TRecord' && Object.prototype.hasOwnProperty.call(resolved.fields, propName)) {
    // If this field carries a stored Scheme (recorded at annotated
    // member-assignment time), re-instantiate it freshly per use site.
    // This makes call-site argument unification AND constraint validation
    // happen at THIS access, instead of reusing the assignment-site
    // instantiation.  Works for any access path — direct (`Param.Query`),
    // aliased (`const A = Param; A.Query`), or via a returned record —
    // because the metadata travels with the record value itself.
    if (resolved.fieldSchemes && Object.prototype.hasOwnProperty.call(resolved.fieldSchemes, propName)) {
      const fresh = engine.instantiateWithConstraints(
        resolved.fieldSchemes[propName], node, undefined);
      engine.recordNodeType(node.property, fresh);
      return fresh;
    }
    // Fallback: dotted-name annotation lookup (covers cases where the
    // record's `fieldSchemes` map wasn't populated — e.g. when the
    // assignment didn't go through the annotated branch but the
    // annotation still exists on the dotted name).
    if (node.object.type === 'Identifier') {
      const dottedName = `${(node.object as estree.Identifier).name}.${propName}`;
      const ann = engine.annotationMap.get(dottedName);
      if (ann?.scheme) {
        const fresh = engine.instantiateWithConstraints(ann.scheme, node, ann);
        engine.recordNodeType(node.property, fresh);
        return fresh;
      }
    }
    const fieldType = resolved.fields[propName];
    engine.recordNodeType(node.property, fieldType);
    return fieldType;
  }

  // Record type but field doesn't exist → fall back to Object.prototype
  // built-ins (`toString`, `valueOf`, …) before reporting a missing field.
  if (resolved.tag === 'TRecord') {
    const builtin = objectPrototypeMethodType(propName);
    if (builtin) {
      engine.recordNodeType(node.property, builtin);
      return builtin;
    }

    // User-defined `Object#method` (e.g. `Object#concat`) resolves on *any*
    // record form (`{}`, `{a}`, `{...a}`, `{[i]::a}`, `{x::T}`).  The receiver
    // row stored on the method entry is unified with the actual record so its
    // fields bind; the label↔row bridge (unify.ts) reconciles the differing
    // record spellings.
    const objEntry = lookupMethod('Object', propName);
    if (objEntry && !objEntry.isStatic) {
      if (objEntry.recordReceiver && objEntry.recordMethodType && objEntry.recordScheme) {
        const synthAnn = {
          receiver: objEntry.recordReceiver,
          methodType: objEntry.recordMethodType,
          scheme: objEntry.recordScheme,
        } as unknown as TypeAnnotation;
        const { thisType, expectedType } = engine.coordinateInstantiate(synthAnn);
        engine.unifyWithDiagnostic(thisType, resolved, node.object as AstNode);
        const methodType = engine.resolve(expectedType);
        engine.recordNodeType(node.property, methodType);
        engine.methodSignatures.set(
          node.property.start,
          `Object#${propName} :: ${prettyTypeToString(methodType)}`,
        );
        return methodType;
      }
      // Shorthand property/method annotation: `Object#prop :: T`.
      const methodType = objEntry.factory([]);
      engine.recordNodeType(node.property, methodType);
      engine.methodSignatures.set(
        node.property.start,
        `Object#${propName} :: ${prettyTypeToString(methodType)}`,
      );
      return methodType;
    }

    // An open record whose row is still a free variable gains the field:
    // `{ paid :: Boolean, ...r }` (a library signature such as
    // `prop :: k -> { [k] :: a, ...r } -> a`, applied before the data is
    // known) read as `o.total` becomes `{ paid :: Boolean, total :: t, ...r' }`.
    // The row of a parameter checked against its own annotation is that
    // annotation's promise: a field outside it stays an error.
    if (resolved.rest && (resolved.rest.tag === 'TVar' || resolved.rest.tag === 'TRow')
        && !isSkolem(resolved.rest) && !engine.rigidRowIds.has(resolved.rest.id)) {
      const fieldType = tVar();
      try {
        const extension = tOpenRecord({ [propName]: fieldType }, tRow(resolved.rest.tag === 'TRow' ? resolved.rest.name : undefined));
        engine.subst = engine.subst.compose(unify(engine.subst.apply(resolved.rest), extension));
        const applied = engine.subst.apply(fieldType);
        engine.recordNodeType(node.property, applied);
        return applied;
      } catch (e) {
        if (!(e instanceof UnificationError)) throw e;
      }
    }

    engine.addDiag(`Property '${propName}' does not exist on type '${typeToString(resolved)}'`, node.property);
    const errType = tVar();
    engine.recordNodeType(node.property, errType);
    return errType;
  }

  // Union type: check each member for the property.
  if (isUnion(resolved) && resolved.args.length > 0) {
    return inferUnionPropertyAccess(engine, node, resolved, propName);
  }

  // Check registry for container/type methods (instance methods on TCon values)
  if (resolved.tag === 'TCon') {
    // Open index-signature object `Object k a` (≅ `{ [k] :: a }`): every key
    // resolves to the homogeneous value type `a`.  Used by e.g. `process.env`
    // (`process.env.NODE_ENV :: String`).  Prototype methods (`toString`,
    // `valueOf`, …) and `.constructor` still resolve normally.
    if (resolved.name === 'Object' && resolved.args.length === 2 && propName !== 'constructor') {
      const builtin = objectPrototypeMethodType(propName);
      if (builtin) {
        engine.recordNodeType(node.property, builtin);
        return builtin;
      }
      const valueType = engine.subst.apply(resolved.args[1]);
      engine.recordNodeType(node.property, valueType);
      return valueType;
    }

    // Check for kind-variable constraint methods first
    const kv = parseKvName(resolved.name);
    if (kv) {
      // .constructor on a kv-constrained type: return TypeRep wrapping
      // the full applied type (e.g. TypeRep (f a)).  Constraints are
      // looked up from the inner type's kv var during method access.
      if (propName === 'constructor') {
        const typeRepType = tCon(T_TYPEREP, [resolved]);
        engine.recordNodeType(node.property, typeRepType);
        return typeRepType;
      }

      const constraintMethod = lookupConstraintMethod(engine, kv.varId, propName, resolved, node);
      if (constraintMethod) return constraintMethod;
      // Kind variable with no matching constraint method — emit a diagnostic
      // if there's a constraint for this kv.
      const cNames = resolveKvConstraintNames(engine.kvConstraints, engine.subst, kv.varId, resolved.name);
      // Also check applied kind * constraints (e.g. Semigroup (s a))
      const ctorCNames = resolveKvConstraintNames(engine.kvConstructorConstraints, engine.subst, kv.varId, resolved.name);
      const kindStarCtorNames = (ctorCNames ?? []).filter(cn => {
        const baseName = constraintBaseName(cn);
        const def = lookupConstraint(baseName);
        return def?.expectedKind === '*';
      });
      const allConstraintNames = [...(cNames ?? []), ...kindStarCtorNames];
      if (allConstraintNames.length > 0 && !isBuiltInJsProperty(propName)) {
        return recordPropertyError(engine, node.property,
          `Property '${propName}' does not exist on constraint '${allConstraintNames.join(', ')}'`);
      }
      const kvErr = tVar();
      engine.recordNodeType(node.property, kvErr);
      return kvErr;
    }

    // TypeRep member access: static constraint methods on the type-rep.
    if (resolved.name === T_TYPEREP && resolved.args.length === 1) {
      return inferTypeRepPropertyAccess(engine, node, resolved, propName, env);
    }

    // .constructor on a concrete TCon
    if (propName === 'constructor') {
      const ctorResult = inferTConConstructorAccess(engine, node, resolved, env);
      if (ctorResult) return ctorResult;
    }

    // Private member access check: `obj.priv` from outside the class /
    // prototype is an error.  `this.priv` from inside (where `this` is
    // bound to the same TCon) is allowed.  Method/field still resolves
    // normally so hover and signature help work.
    if (isMethodPrivate(resolved.name, propName) && node.object.type !== 'ThisExpression') {
      engine.addDiag(
        `Property '${propName}' is private to type '${resolved.name}'`,
        node.property);
    }

    const entry = lookupMethod(resolved.name, propName);
    if (entry && !entry.isStatic) {
      return inferTConInstanceMethod(engine, node, resolved, propName, entry, env);
    }
    // Static method on the TCon value (e.g. `this.constructor.of(x)` after
    // `.constructor` was typed as the sumtype value).  When the receiver is
    // a value typed as `Either e a`, lookups like `.of` should still find
    // `Either.of`.  This mirrors the identifier-based path in
    // `inferStaticMethodAccess`.
    if (entry && entry.isStatic) {
      const methodType = entry.scheme?.constraints?.length
        ? engine.instantiateWithConstraints(entry.scheme, node)
        : entry.factory([]);
      engine.recordNodeType(node.property, methodType);
      engine.methodSignatures.set(
        node.property.start,
        `${resolved.name}.${propName} :: ${prettyTypeToString(methodType)}`,
      );
      return methodType;
    }

    // No matching instance method found on this TCon type.
    // If the type has any registered methods at all, the property is likely
    // a mistake — emit a diagnostic.  Skip properties that were assigned
    // via `this.prop = ...` in the constructor (unannotated but valid).
    if (!entry) {
      // DOM/Fetch nominal types (Document, Element, Response, …) carry a
      // deliberately COMPACT method catalogue — anything not listed silently
      // resolves to `Any` instead of erroring, mirroring the open-world
      // philosophy for the huge browser API surface (see domGlobals.ts).
      if (hasAnyFallbackMethods(resolved.name) && !isBuiltInJsProperty(propName)) {
        engine.recordNodeType(node.property, tAnyType);
        return tAnyType;
      }
      const knownNames = getMethodNames(resolved.name);
      if (knownNames.length > 0
          && !isBuiltInJsProperty(propName)
          && !engine.constructorProperties.has(`${resolved.name}#${propName}`)) {
        // Record-style sumtype variants name their carried fields, e.g.
        //   `Component :: | Engine { ext :: String, handler :: EngineFn } | ...`
        // A `Component ~>` method (typically `matchWith`) may read those
        // fields off `this` even though no constructor assigns them and no
        // `Component#ext` annotation was written.  Accept such a field access
        // automatically from the declaration and surface the declared field
        // type on hover.
        const recordFieldType = getVariantRecordFields(resolved.name).get(propName);
        if (recordFieldType !== undefined) {
          engine.methodSignatures.set(
            node.property.start,
            `${resolved.name}#${propName} :: ${recordFieldType}`,
          );
          return recordSuppressedProperty(engine, node.property);
        }
        return recordPropertyError(engine, node.property,
          `Property '${propName}' does not exist on type ${prettyTypeToString(resolved)}`);
      }
    }
  }

  // Check registry for static methods using the identifier name (e.g. Box.fromPair)
  if (node.object.type === 'Identifier') {
    const staticResult = inferStaticMethodAccess(engine, node, propName);
    if (staticResult) return staticResult;
  }

  // If it's a type var, first check for constraint-based method lookup.
  // When the TVar has a constraint (e.g. Monad m), static method access on
  // the bare type variable is blocked — use TypeRep m instead.
  // However, for kind * constraints (e.g. Semigroup s), instance methods
  // should be accessible directly since s is a concrete value, not a constructor.
  if (resolved.tag === 'TVar') {
    const tvarResult = inferTVarPropertyAccess(engine, node, resolved, propName, objectType);
    if (tvarResult) return tvarResult;
  }

  // Property access on a function type (TFun): look up static methods by
  // the function's return type (e.g. building.constructor.create).
  if (resolved.tag === 'TFun') {
    const funBuiltin = inferTFunBuiltinMethod(engine, node, resolved, propName);
    if (funBuiltin) return funBuiltin;
    const funStaticResult = inferFunStaticMethodAccess(engine, node, resolved, propName);
    if (funStaticResult) return funStaticResult;
  }

  // Wildcard type (e.g. *:a from an unconstrained annotation parameter) —
  // the type is explicitly generic, so property access cannot be resolved.
  // Mark for hover suppression but do not emit a diagnostic — the user may
  // intentionally use a generic parameter without constraints.
  // A rigid skolem (the parameter of a body checked against its annotation)
  // is the same generic parameter, so it is treated alike.
  if (isWildcard(resolved) || isSkolem(resolved)) {
    return recordSuppressedProperty(engine, node.property);
  }

  // Property access on an unconstrained type variable — we don't know if
  // this property exists.  Record a dummy type so the property node wins
  // as most-specific hover match, then mark for suppression.  Also park the
  // access for late re-resolution: a later unification may pin the receiver
  // (e.g. `myMap(s => s.length)(["aa"])` — the data argument arrives after
  // the callback), at which point the member lookup is retried and the
  // dummy var is unified with the real member type.
  if (resolved.tag === 'TVar') {
    const suppressed = recordSuppressedProperty(engine, node.property);
    engine.deferredMemberAccesses.push({
      objType: resolved,
      propName,
      resultType: suppressed,
      propStart: node.property.start,
      node: node.property,
    });
    return suppressed;
  }

  const fallback = tVar();
  engine.recordNodeType(node.property, fallback);
  return fallback;
}

// -----------------------------------------------------------------------
// inferMemberExpression helpers
// -----------------------------------------------------------------------

/** Handle property access on a union type: check each member and collect results. */
function inferUnionPropertyAccess(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TCon' }, propName: string,
): Type {
  // Variant-union shortcut (e.g. `Just a | Nothing`): when every member is
  // a variant of the same parent sumtype and the parent has `propName`
  // (typically `.of` or another inherited static), resolve through the
  // parent ONCE so we get a single sharp signature instead of a union of
  // freshly-instantiated factories.
  {
    const variantMembers = resolved.args.filter(
      (m): m is Type & { tag: 'TCon' } => m.tag === 'TCon' && m.name !== T_UNION,
    );
    if (variantMembers.length === resolved.args.length && variantMembers.length > 0) {
      const parentNames = variantMembers.map(m => getParentTypeName(m.name));
      const parent = parentNames[0];
      if (parent && parentNames.every(n => n === parent)) {
        const entry = lookupMethod(parent, propName);
        if (entry) {
          const parentArity = getTypeArity(parent);
          const parentArgs: Type[] = Array.from({ length: parentArity }, () => tVar());
          const methodType = entry.factory(parentArgs);
          engine.recordNodeType(node.property, methodType);
          return methodType;
        }
      }
    }
  }
  const memberResults: Type[] = [];
  const badMembers: string[] = [];
  // Track whether we silently skipped any TFun branches.  Function values
  // in an overload union (from repeated `Name :: ...` declarations) have
  // no fields, so accessing a property on the union is interpreted as
  // accessing it on the non-callable side; we don't want to flag the
  // function branches as "missing property".
  let skippedFunBranch = false;
  // Track unresolved (type-variable) members.  A member that is still an
  // unconstrained variable — e.g. the default export of a module that could
  // not be inferred — says nothing about the property either way.  Property
  // access on a single TVar is permissive, so stay consistent for unions
  // instead of flagging every unresolved member as "missing property".
  let skippedUnresolvedBranch = false;
  // A union with an `Any` member is `Any` for property access: the unknown
  // member may have the property (TypeScript's `__importDefault` helper
  // returns `{ default :: a } | a` with `a := Any` for `require (…)`).
  if (resolved.args.some(m => isAnyType(engine.maybeExpandAlias(m)))) {
    engine.recordNodeType(node.property, tAnyType);
    return tAnyType;
  }
  for (const member of resolved.args) {
    const expanded = engine.maybeExpandAlias(member);
    if (expanded.tag === 'TRecord' && propName in expanded.fields) {
      memberResults.push(expanded.fields[propName]);
    } else if (expanded.tag === 'TCon' && expanded.name !== T_UNION) {
      let entry = lookupMethod(expanded.name, propName);
      let lookupArgs = expanded.args;
      // Variant member of a sumtype: try the parent sumtype for inherited
      // methods (e.g. `Maybe.of` on a `Just a | Nothing` union).
      if (!entry) {
        const parentName = getParentTypeName(expanded.name);
        if (parentName) {
          entry = lookupMethod(parentName, propName);
          if (entry) {
            // Use parent's type-arg arity rather than the variant's so the
            // factory receives the right number of args.
            const parentArity = getTypeArity(parentName);
            lookupArgs = Array.from({ length: parentArity }, (_, i) => expanded.args[i] ?? tVar());
          }
        }
      }
      if (entry) {
        const methodType = entry.factory(lookupArgs);
        // Identity-on-receiver methods (e.g. `Table p ~> [a] -> Table p`)
        // declare that calling the method preserves the receiver shape.
        // When the receiver is part of an overloaded-constructor union
        // (skippedFunBranch === true), preserving only the matched
        // member discards the other overloads; rewrite the method's
        // return type to the WHOLE union so downstream call sites
        // still see all overloads (e.g. selector overloads).
        if (
          methodType.tag === 'TFun'
          && structuralEquals(methodType.result, expanded)
        ) {
          memberResults.push({ ...methodType, result: resolved });
        } else {
          memberResults.push(methodType);
        }
      } else {
        badMembers.push(prettyTypeToString(member));
      }
    } else if (expanded.tag === 'TFun') {
      skippedFunBranch = true;
    } else if (expanded.tag === 'TVar' || expanded.tag === 'TRow') {
      skippedUnresolvedBranch = true;
    } else {
      badMembers.push(prettyTypeToString(member));
    }
  }
  if (badMembers.length > 0) {
    // Overloaded-constructor unions mix value-shapes with at least one
    // callable (TFun) overload — e.g. query-builder's
    //   `Caregiver :: ({ props :: … } | Table CaregiverRow | ([CaregiverSelector] -> QueryTag p (Picked …)))`.
    // A method like `Table#addProps` is defined for the `Table` view only;
    // the `{props}` view is metadata and the call-overload is irrelevant
    // for property access.  When at least one branch DID resolve the
    // property AND the union carries a TFun overload, treat that as a
    // narrowed access (pick the resolving member) rather than flagging
    // the metadata branches as "missing".  Without this, the failing
    // diagnostic causes the host binding (`const U = X.addProps([...])`)
    // to fall back to a bare TVar, which then silently swallows further
    // type errors at every later use site.
    if (memberResults.length > 0 && skippedFunBranch) {
      const resultType = memberResults.length === 1 ? memberResults[0] : tUnion(memberResults);
      engine.recordNodeType(node.property, resultType);
      return resultType;
    }
    engine.addDiag(
      `Property '${propName}' does not exist on type${badMembers.length > 1 ? 's' : ''} ${badMembers.map(m => `'${m}'`).join(', ')} in union '${prettyTypeToString(resolved)}'`,
      node.property,
    );
    const suppressedType = memberResults.length > 0
      ? (memberResults.length === 1 ? memberResults[0] : tUnion(memberResults))
      : tVar();
    engine.recordNodeType(node.property, suppressedType);
    engine.unconstrainedPropAccesses.add(node.property.start);
    return suppressedType;
  }
  if (memberResults.length > 0) {
    const resultType = memberResults.length === 1 ? memberResults[0] : tUnion(memberResults);
    engine.recordNodeType(node.property, resultType);
    return resultType;
  }
  const errType = tVar();
  engine.recordNodeType(node.property, errType);
  // Suppress unconstrainedPropAccess marker only when we silently skipped
  // a TFun branch — that means the overload union was intentionally used
  // for callability, and the access is valid at runtime even if no
  // non-function branch resolved the prop.  Unresolved (TVar) branches are
  // equally inconclusive, so they suppress the marker too.  Otherwise mark
  // as unresolved.
  if (!skippedFunBranch && !skippedUnresolvedBranch) {
    engine.unconstrainedPropAccesses.add(node.property.start);
  }
  return errType;
}

/** Handle TypeRep member access: static constraint methods on TypeRep (f a). */
/**
 * A static reached through a type representative produces values of THAT
 * representative's type: `IdMaybe.of :: a -> IdT m a` through
 * `IdMaybe :: TypeRep (IdT Maybe)` is `a -> IdT Maybe a`.  Unify the leading
 * arguments of the static's result `T …` with the witness `T x1 … xk`
 * (best-effort: a static that returns something else is left alone).
 * Without this the monad of a transformer instance (`StateT (Either)`,
 * `IdT (Maybe)`) was forgotten by every static (`of`, `lift`, `ask`, …).
 */
function bindStaticToWitness(engine: InferenceEngine, staticType: Type, witness: Type & { tag: 'TCon' }): void {
  if (witness.args.length === 0) return;
  const ret = engine.subst.apply(getReturnType(engine.subst.apply(staticType)));
  if (ret.tag !== 'TCon' || ret.name !== witness.name || ret.args.length < witness.args.length) return;
  try {
    for (let i = 0; i < witness.args.length; i++) {
      engine.subst = engine.subst.compose(unify(engine.subst.apply(ret.args[i]), engine.subst.apply(witness.args[i])));
    }
  } catch (e) {
    if (!(e instanceof UnificationError)) throw e;
  }
}

function inferTypeRepPropertyAccess(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TCon' }, propName: string, env: TypeEnv,
): Type {
  const innerType = resolved.args[0];

  // Case 1: inner is a kv TCon (from .constructor on a kv-constrained value)
  if (innerType.tag === 'TCon') {
    const innerKv = parseKvName(innerType.name);
    if (innerKv) {
      const allNames = collectAllKvConstraintNames(
        engine.kvConstraints, engine.kvConstructorConstraints,
        engine.subst, innerKv.varId, innerType.name,
      );
      if (allNames.length > 0) {
        const result = lookupConstraintMethodOnTVar(engine, innerKv.varId, propName, allNames, node);
        if (result) return result;
      }
    } else {
      // Case 1b: inner is a concrete constructor (e.g. `TypeRep Array`,
      // `TypeRep Either`).  The witness IS that constructor, so static
      // methods (`Array.of`, a sumtype's `.of`, …) resolve against the named
      // type, and `.constructor` yields its constructor signature.
      const staticResult = lookupStaticMethodByTypeName(engine, node, innerType.name, propName, true);
      if (staticResult) {
        bindStaticToWitness(engine, staticResult, innerType);
        return staticResult;
      }
      if (propName === 'constructor') {
        const ctorResult = inferTConConstructorAccess(engine, node, innerType, env);
        if (ctorResult) return ctorResult;
      }
    }
  }

  // Case 2: inner is a TVar (from annotation like `TypeRep m`)
  if (innerType.tag === 'TVar') {
    const cNames = engine.kvConstraints.get(innerType.id);
    if (cNames && cNames.length > 0) {
      const result = lookupConstraintMethodOnTVar(engine, innerType.id, propName, cNames, node);
      if (result) return result;
    }
    const appliedCNames = engine.kvConstructorConstraints.get(innerType.id);
    if (appliedCNames && appliedCNames.length > 0) {
      const result = lookupConstraintMethodOnTVar(engine, innerType.id, propName, appliedCNames, node);
      if (result) return result;
    }
  }

  const trErr = tVar();
  engine.recordNodeType(node.property, trErr);
  return trErr;
}

/** Handle .constructor access on a concrete TCon (data types, env lookup). */
function inferTConConstructorAccess(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TCon' }, env: TypeEnv,
): Type | null {
  // For sumtype data types, build a synthetic constructor from the
  // declaration's type vars.  Checked BEFORE env.lookup because when
  // the parent class shares the sumtype name, env.lookup would return
  // the inferred class constructor which doesn't carry the correct
  // return type for static method lookup.
  if (isDataType(resolved.name)) {
    const dt = getDataType(resolved.name)!;
    // Sumtype `.constructor` is modelled as the union of its variant
    // constructors (e.g. `Maybe`'s `.constructor` -> `Just a | Nothing`).
    // This makes the available shapes immediately visible, lets static
    // method lookup (`.of`) resolve through either branch, and yields a
    // helpful `Just a | Nothing is not callable` diagnostic on `new`.
    const args = dt.decl.typeVars.map(() => tVar());
    const variantTypes = dt.decl.variants.map(v => {
      const vArgs = v.fields.map(f => {
        const idx = dt.decl.typeVars.indexOf(f);
        return idx >= 0 ? args[idx] : tVar();
      });
      return tCon(v.name, vArgs);
    });
    const ctorType = tUnion(variantTypes);
    engine.recordNodeType(node.property, ctorType);
    // Stash the parent sumtype name so hover can surface
    // `Just a | Nothing` next to the constructor type.
    if (node.property.start !== undefined) {
      engine.constructorParentSumtype.set(node.property.start, resolved.name);
      // Freeze a pretty-printed snapshot of the union BEFORE any later
      // unification (e.g. `new x.constructor(...)` failing) can poison
      // its TVars to `$error`, so hover can still display `Just a | Nothing`.
      engine.frozenPropertyTypeStr.set(
        node.property.start,
        prettyTypeToString(ctorType),
      );
    }
    return ctorType;
  }
  // Arrow-factory binding (`const Pair = (a,b) => ({...})`): at runtime
  // its instances' `.constructor` is `Object`, not the factory.  Reflect
  // that so `new p.constructor(...)` doesn't get typed as `Pair`.
  if (engine.constructorProvenance.get(resolved.name) === 'arrow-factory') {
    const ctorType = tCon('Object', []);
    engine.recordNodeType(node.property, ctorType);
    return ctorType;
  }
  // Built-in JS types (`Array`, `String`, `Number`, `Function`, …):
  // synthesise a constructor signature that reflects the type's runtime
  // constructor.  For Array, the element type is taken from the receiver
  // so `[a].constructor` is shaped `(..., Number | a) -> [a]`.
  const builtinCtor = builtinConstructorType(resolved.name, resolved.args);
  if (builtinCtor) {
    engine.recordNodeType(node.property, builtinCtor);
    if (node.property.start !== undefined) {
      engine.builtinCtorKind.set(node.property.start, resolved.name);
    }
    return builtinCtor;
  }
  const ctorScheme = env.lookup(resolved.name);
  if (ctorScheme) {
    const ctorType = instantiate(ctorScheme);
    engine.recordNodeType(node.property, ctorType);
    return ctorType;
  }
  return null;
}

/** Handle static method lookup by identifier name (e.g. Box.fromPair). */
function inferStaticMethodAccess(
  engine: InferenceEngine, node: estree.MemberExpression, propName: string,
): Type | null {
  const objName = (node.object as estree.Identifier).name as string;
  return lookupStaticMethodByTypeName(engine, node, objName, propName, false);
}

/** Handle static method lookup on TFun by return type. */
function inferFunStaticMethodAccess(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TFun' }, propName: string,
): Type | null {
  const retType = engine.subst.apply(getReturnType(resolved));
  if (retType.tag !== 'TCon') return null;
  return lookupStaticMethodByTypeName(engine, node, retType.name, propName, true);
}

/**
 * `Function.prototype` methods on a TFun value.  Unlike the generic
 * `Function` TCon entries (which lose the return type), these preserve the
 * function's own return type so that e.g. `({}).toString.call(x)` is
 * typed `String` rather than a fresh TVar.
 */
function inferTFunBuiltinMethod(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TFun' }, propName: string,
): Type | null {
  const retType = getReturnType(resolved);
  let methodType: Type | null = null;
  switch (propName) {
    case 'call':
      // (thisArg, ...args) -> R — modelled as `a -> R` (this engine has no
      // variadic; callers typically write `f.call(thisArg, …)` and only the
      // return type matters for downstream inference).
      methodType = tFun(tVar('a'), retType);
      break;
    case 'apply':
      // (thisArg, [args]) -> R — modelled as `a -> R`.
      methodType = tFun(tVar('a'), retType);
      break;
    case 'bind':
      // (thisArg, ...args) -> sameFunction
      methodType = tFun(tVar('a'), resolved);
      break;
    case 'length':
      methodType = tNumber;
      break;
    case 'name':
      methodType = tString;
      break;
    case 'constructor': {
      const ctor = builtinConstructorType('Function', []);
      if (!ctor) return null;
      engine.recordNodeType(node.property, ctor);
      if (node.property.start !== undefined) {
        engine.builtinCtorKind.set(node.property.start, 'Function');
      }
      engine.methodSignatures.set(
        node.property.start,
        `Function.constructor :: ${prettyTypeToString(ctor)}`,
      );
      return ctor;
    }
    default:
      return null;
  }
  engine.recordNodeType(node.property, methodType);
  engine.methodSignatures.set(
    node.property.start,
    `Function.${propName} :: ${prettyTypeToString(methodType)}`,
  );
  return methodType;
}

/**
 * Shared core: look up `propName` on `typeName` and record its instantiated
 * type at the property node.  When `requireStatic` is true, only entries
 * marked `isStatic` are accepted.
 */
function lookupStaticMethodByTypeName(
  engine: InferenceEngine,
  node: estree.MemberExpression,
  typeName: string,
  propName: string,
  requireStatic: boolean,
): Type | null {
  const entry = lookupMethod(typeName, propName);
  if (!entry || (requireStatic && !entry.isStatic)) return null;
  const methodType = entry.scheme?.constraints?.length
    ? engine.instantiateWithConstraints(entry.scheme, node)
    : entry.factory([]);
  engine.recordNodeType(node.property, methodType);
  engine.methodSignatures.set(
    node.property.start,
    `${typeName}.${propName} :: ${prettyTypeToString(methodType)}`,
  );
  return methodType;
}

/** Handle computed property access: arr[i], record["field"], etc. */
function inferComputedAccess(
  engine: InferenceEngine, node: estree.MemberExpression, env: TypeEnv, objectType: Type, resolved: Type,
): Type {
  const indexType = inferExpression(engine, node.property, env);

  if (resolved.tag === 'TCon' && resolved.name === T_ARRAY && resolved.args.length === 1) {
    engine.unifyWithDiagnostic(indexType, tNumber, node.property);
    let elemType = resolved.args[0];
    elemType = engine.maybeExpandAlias(elemType);
    return elemType;
  }

  // Indexing an ABSTRACT constrained container (`xs[0]` with `xs :: f a`,
  // `Functor f`): no constraint promises index access, so this is the same
  // error as an unknown member (`xs.length`).  Inside an Array guard the value
  // is `[a]` (local `f ≡ Array`) and takes the Array case above.
  if (resolved.tag === 'TCon') {
    const kv = parseKvName(resolved.name);
    if (kv && resolved.args.length > 0) {
      const cNames = resolveKvConstraintNames(engine.kvConstraints, engine.subst, kv.varId, resolved.name) ?? [];
      if (cNames.length > 0) {
        return recordPropertyError(engine, node.property,
          `Index access does not exist on constraint '${cNames.join(', ')}'`);
      }
    }
  }

  if (resolved.tag === 'TVar') {
    // If the index resolves to a String, treat the object as a record-like
    // value (obj[stringKey]) and don't force-unify with Array. This avoids
    // spurious "Cannot unify 'String' with 'Number'" diagnostics when the
    // object's type is unknown.
    const resolvedIndex = engine.subst.apply(indexType);
    if (resolvedIndex.tag === 'TCon' && resolvedIndex.name === tString.name) {
      return tVar();
    }
    // Index type not known yet either (`obj => key => obj[key]`, or a
    // callback whose key is only fixed by a later argument, as in FP-library
    // `foldMap (key => spec[key] …) (Object.keys (spec))`): committing the
    // object to Array here rejected every record/dictionary argument later.
    // Leave both open.
    if (resolvedIndex.tag === 'TVar') {
      return tVar();
    }
    const elemType = tVar();
    engine.unifyWithDiagnostic(objectType, tArray(elemType), node.object);
    engine.unifyWithDiagnostic(indexType, tNumber, node.property);
    return engine.subst.apply(elemType);
  }

  if (resolved.tag === 'TRecord' && node.property.type === 'Literal' && typeof node.property.value === 'string') {
    const key = node.property.value;
    if (key in resolved.fields) {
      const fieldType = resolved.fields[key];
      engine.recordNodeType(node.property, fieldType);
      return fieldType;
    }
    engine.addDiag(`Property '${key}' does not exist on type '${typeToString(resolved)}'`, node.property);
    return tVar();
  }

  // Label-polymorphic record indexed by a non-literal key (e.g. inside
  // `Object.keys(obj).reduce((acc, k) => obj[k]…)`).  When the record
  // carries a `{ [k] :: T }` group, the bracketed access yields `T` —
  // bind the labelField's label-var to the index type if it's a TLabel
  // var so subsequent unifications stay linked.
  if (resolved.tag === 'TRecord' && resolved.labelFields && resolved.labelFields.length > 0) {
    const resolvedIndex = engine.subst.apply(indexType);
    // Only treat the index as a label when it's a String, a TLabel, or a TVar.
    const indexLooksLikeKey =
      resolvedIndex.tag === 'TLabel' ||
      (resolvedIndex.tag === 'TCon' && resolvedIndex.name === tString.name) ||
      resolvedIndex.tag === 'TVar';
    if (indexLooksLikeKey) {
      const lf = resolved.labelFields[0];
      // If the index is a TLabel-var, link it to this labelField's label.
      if (resolvedIndex.tag === 'TLabel' && resolvedIndex.kind === 'var') {
        try { engine.unifyWithDiagnostic(resolvedIndex, lf.label, node.property); } catch { /* swallow */ }
      }
      return engine.subst.apply(lf.type);
    }
  }

  // A dictionary `Object k a` (also spelled with a concrete key type such as
  // `Object String a`) indexed by a non-literal key yields its value type `a`
  // — as for the label-record form above.  Without this the lookup returned
  // a fresh variable and every check on the result was lost (`handlers[name]
  // (payload).bichain (f, g)` went unreported).
  if (isAppliedObject(resolved)) {
    const resolvedIndex = engine.subst.apply(indexType);
    const indexLooksLikeKey =
      resolvedIndex.tag === 'TLabel' ||
      (resolvedIndex.tag === 'TCon' && resolvedIndex.name === tString.name) ||
      resolvedIndex.tag === 'TVar';
    if (indexLooksLikeKey) return engine.subst.apply(resolved.args[1]);
  }

  return tVar();
}

/** Handle instance method lookup on a TCon, including chain isolation for sumtype types. */
function inferTConInstanceMethod(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TCon' }, propName: string, entry: MethodEntry, env: TypeEnv,
): Type {
  let methodArgs = resolved.args;
  let displayType: Type = resolved;
  const isChainIsolated = node.object.type === 'CallExpression';
  const dt = isChainIsolated && isDataType(resolved.name) ? getDataType(resolved.name) : null;
  if (isChainIsolated) {
    if (dt && dt.decl.typeVars.length > 0) {
      methodArgs = resolved.args.map((arg, i) => {
        const applied = engine.subst.apply(arg);
        if (applied.tag === 'TVar') return tVar(dt.decl.typeVars[i]);
        return applied;
      });
      displayType = tCon(resolved.name, methodArgs);
    } else {
      const freshened = freshenType(resolved);
      if (freshened.tag === 'TCon') {
        methodArgs = freshened.args;
        displayType = freshened;
      }
    }
  }
  let methodType: Type;
  let constraintPreBindings: Map<string, Type> | null = null;
  if (entry.scheme?.constraints?.length && entry.receiverVarNames?.length) {
    // Constrained instance methods (e.g. `Prop#eq :: Runnable a r => Prop t a ~> r -> Prop t a`):
    // instantiate via the engine so pending constraints are registered with
    // receiver type variables pre-bound to the actual container type
    // arguments. This makes `id.eq("een")` (where `id :: Prop Tag Number`)
    // detect that `String` does not satisfy `Runnable Number r`.
    const preBindings = new Map<string, Type>();
    for (let i = 0; i < entry.receiverVarNames.length && i < methodArgs.length; i++) {
      const name = entry.receiverVarNames[i];
      if (name) preBindings.set(name, methodArgs[i]);
    }
    methodType = engine.instantiateWithConstraints(entry.scheme, node, undefined, false, preBindings);
    constraintPreBindings = preBindings;
  } else {
    methodType = entry.factory(methodArgs);
  }

  // For sumtype chain isolation, disconnect receiver-position values in callback return types
  if (isChainIsolated && isDataType(resolved.name) && methodType.tag === 'TFun') {
    const callbackType = methodType.param;
    if (callbackType.tag === 'TFun') {
      const receiverVarIds = new Map<number, string>();
      const receiverConcreteStrings = new Map<string, string>();
      for (let i = 0; i < methodArgs.length; i++) {
        const ma = methodArgs[i];
        if (ma.tag === 'TVar') {
          receiverVarIds.set(ma.id, dt!.decl.typeVars[i] ?? ma.name);
        } else {
          receiverConcreteStrings.set(typeToString(ma), dt!.decl.typeVars[i] ?? 'a');
        }
      }
      const replaceReceiverArgs = (t: Type): Type =>
        mapType(t, node =>
          node.tag === 'TVar' && receiverVarIds.has(node.id) ? tVar(receiverVarIds.get(node.id)) :
          node.tag === 'TCon' && receiverConcreteStrings.has(typeToString(node)) ? tVar(receiverConcreteStrings.get(typeToString(node))!) :
          undefined,
        );
      const freshenedReturn = replaceReceiverArgs(callbackType.result);
      methodType = tFun(tFun(callbackType.param, freshenedReturn), methodType.result);
    }
  }

  // sumtype variant property narrowing
  if (node.object.type === 'ThisExpression' && isUnion(methodType)) {
    methodType = narrowSumtypePropertyUnion(methodType, resolved, methodArgs, env);
  } else if (node.object.type === 'Identifier' && isUnion(methodType)) {
    const variantEnvKey = `__sumtypeVariant_${node.object.name}`;
    methodType = narrowSumtypePropertyUnion(methodType, resolved, methodArgs, env, variantEnvKey);
  }

  engine.recordNodeType(node.property, methodType);
  // Build the hover signature.  When the method has constraints (e.g.
  // `Runnable String r =>`), prepend them with the receiver vars
  // substituted by the actual container type arguments so the hover
  // reflects the same constraints used during type-checking.
  let constraintPrefix = '';
  if (entry.scheme?.constraints?.length && constraintPreBindings) {
    const substArg = (t: Type): Type =>
      mapType(t, n => (n.tag === 'TVar' && n.name && constraintPreBindings!.has(n.name))
        ? constraintPreBindings!.get(n.name)
        : undefined);
    const substConstraints = entry.scheme.constraints.map(c => ({
      ...c,
      positionalArgs: c.positionalArgs?.map(substArg),
      unionAlternatives: c.unionAlternatives?.map(substArg),
    }));
    // Render constraints via schemeToString using a sentinel TVar; strip
    // the sentinel back off to get just the `C1, C2 => ` prefix.
    const sentinelName = '__HOVER_CONSTRAINT_SENTINEL__';
    const rendered = schemeToString({
      vars: [],
      type: tVar(sentinelName),
      constraints: substConstraints,
    });
    const idx = rendered.lastIndexOf(sentinelName);
    if (idx >= 0) constraintPrefix = rendered.slice(0, idx);
  }
  engine.methodSignatures.set(
    node.property.start,
    engine.scrubSkolemString(
      `${resolved.name}#${propName} :: ${constraintPrefix}${prettyTypeToString(displayType)} ~> ${prettyTypeToString(methodType)}`,
    ),
  );
  return methodType;
}

/** Handle property access on a TVar: constraint methods, probe candidates.
 *  Returns null if no match found (caller falls through to later checks). */
function inferTVarPropertyAccess(
  engine: InferenceEngine, node: estree.MemberExpression,
  resolved: Type & { tag: 'TVar' }, propName: string, objectType: Type,
): Type | null {
  const constraintNames = engine.kvConstraints.get(resolved.id);
  const appliedNames = engine.kvConstructorConstraints.get(resolved.id);
  const allNames = [...(constraintNames ?? []), ...(appliedNames ?? [])];

  if (allNames.length > 0) {
    if (propName === 'constructor') {
      const typeRepType = tCon(T_TYPEREP, [resolved]);
      engine.recordNodeType(node.property, typeRepType);
      return typeRepType;
    }

    let isStaticMethod = false;
    let isInstanceMethod = false;
    let matchedConstraint = '';
    let instanceMethodDef: import('../registries/constraintRegistry').ConstraintDef | null = null;
    let instanceMethodReq: { name: string; signature: string } | null = null;
    for (const cName of allNames) {
      const baseName = constraintBaseName(cName);
      const def = lookupConstraint(baseName);
      if (!def) continue;
      const effectiveMethods = getEffectiveMethods(baseName);
      const req = effectiveMethods.find(m => m.name === propName);
      if (req) {
        if (req.signature.includes('~>')) {
          isInstanceMethod = true;
          matchedConstraint = baseName;
          instanceMethodDef = def;
          instanceMethodReq = req;
        } else {
          isStaticMethod = true;
        }
      }
    }
    if (isStaticMethod) {
      const varName = resolved.name || 'm';
      return recordPropertyError(engine, node.property,
        `Cannot access constraint method '${propName}' on a bare type variable. Annotate the parameter as 'TypeRep ${varName}' to enable constructor method access.`);
    }
    if (isInstanceMethod && instanceMethodDef && instanceMethodReq) {
      if (instanceMethodDef.expectedKind === '*') {
        const methodType = lookupConstraintInstanceMethodOnTVar(
          engine, resolved, propName, instanceMethodDef, instanceMethodReq, node);
        if (methodType) return methodType;
      }
      return recordPropertyError(engine, node.property,
        `'${propName}' is an instance method on constraint '${matchedConstraint}' and cannot be called on the type constructor`);
    } else {
      const displayNames = allNames.map(n => constraintBaseName(n));
      return recordPropertyError(engine, node.property,
        `Property '${propName}' does not exist on constraint '${displayNames.join(', ')}'`);
    }
  }

  // Probe all registered types for this property/method
  const candidates = findMethodCandidates(propName);
  if (candidates.length === 1) {
    const [typeName, entry] = candidates[0];
    // Accessing a member must NOT nominally pin an otherwise-unconstrained
    // receiver to the member's owner.  A single registered owner — whether a
    // BUILT-IN container (Array, String, …) OR a user-defined data type (e.g.
    // `Pair` owning `fst`/`snd`) — is not sufficient evidence to coerce an
    // unconstrained type variable into that type.  Doing so mis-infers values
    // whose real type is established elsewhere (annotations, chained
    // declarations, `::rep`, or a later application): e.g. `pair.fst` /
    // `pair.snd` in `map(pair => …)` must leave `pair` free rather than assume
    // it is a `Pair` just because `Pair` happens to be the sole registered
    // owner of `fst`/`snd`.  Local annotations / chained declarations / `::rep`
    // take precedence; the registry is consulted only when the receiver type is
    // already known.  Fall through so the caller records a suppressed property.
    //
    // EXCEPTION: container-IDENTITY methods (`Map#get`, `Set#add`) remain a
    // strong enough signal to coerce.  Unlike a plain accessor or a generic FP
    // name, these operations are owned by essentially one container, so
    // `x.get(k)` on an unknown `x` back-constrains `x` to `Map k v` (cascades
    // so nested `.set`/`.has`/`.get` resolve and value types tie together).
    if (!isContainerIdentityMethod(typeName, propName)) {
      return null;
    }
    const arity = getTypeArity(typeName);
    const freshArgs = freshVars(arity);
    engine.unifyWithDiagnostic(objectType, tCon(typeName, freshArgs), node.object);
    const resolvedArgs = freshArgs.map((a) => engine.subst.apply(a));
    const methodType = entry.factory(resolvedArgs);
    engine.recordNodeType(node.property, methodType);
    const resolvedObj = engine.subst.apply(objectType);
    engine.methodSignatures.set(
      node.property.start,
      `${typeName}#${propName} :: ${prettyTypeToString(resolvedObj)} ~> ${prettyTypeToString(methodType)}`,
    );
    return methodType;
  }
  // Several owners (e.g. `name` on Error, Function and a library's `Table`):
  // no evidence either — the same rule as the single-owner case.  The
  // receiver stays free and the access is recorded as a record field.  Even
  // when every owner agrees on the member type (`String`), returning it
  // without pinning the receiver typed `p => p.name` as `a -> String`, which
  // rejected `{ name: null }` as the argument of a parameter callback.
  return null;
}

// -----------------------------------------------------------------------
// Shared helpers for property-access error handling
// -----------------------------------------------------------------------

/** Built-in JS properties that exist on all objects and should not trigger
 *  "property does not exist" diagnostics. */
function isBuiltInJsProperty(name: string): boolean {
  return name === 'constructor' || name === 'toString' || name === 'valueOf';
}

/**
 * Object.prototype methods that are available on every JS object.  Each
 * entry produces a freshly-constructed Type per access site so polymorphic
 * results (`valueOf :: () -> a`) get a fresh TVar each time and don't
 * accidentally unify across unrelated uses.
 *
 * Used by both inference (`o.toString` returns the right TFun) and
 * completion (`{}.` suggests these names).
 */
export const OBJECT_PROTOTYPE_METHOD_NAMES = [
  'toString',
  'valueOf',
  'hasOwnProperty',
  'isPrototypeOf',
  'propertyIsEnumerable',
] as const;

export function objectPrototypeMethodType(name: string): Type | undefined {
  switch (name) {
    case 'toString':              return tFun(tVoid, tString);
    case 'valueOf':               return tFun(tVoid, tVar('a'));
    case 'hasOwnProperty':        return tFun(tString, tBool);
    case 'isPrototypeOf':         return tFun(tVar('a'), tBool);
    case 'propertyIsEnumerable':  return tFun(tString, tBool);
    case 'constructor':           return builtinConstructorType('Object', []) ?? undefined;
    default:                      return undefined;
  }
}

/**
 * Constructor type for a built-in JS type.  Returned by `.constructor`
 * accesses on values of these built-in types.  For `Array`, the element
 * variable is taken from the receiver so `[a].constructor` is shaped
 * `(..., Number | a) -> [a]` (note: actual call-site widening to a union
 * of literal arg types is handled separately at the CallExpression level).
 */
export function builtinConstructorType(typeName: string, typeArgs: Type[]): Type | null {
  switch (typeName) {
    case 'Array': {
      const elem = typeArgs[0] ?? tVar('a');
      // Variadic shape: `(..., (Number | elem)) -> [elem]`.  The spread
      // tuple holds a single union element which prints as `Number | a`.
      return tFun(tTuple([tSpread, tUnion([tNumber, elem])]), tArray(elem));
    }
    case 'String':  return tFun(tVar('a'), tString);
    case 'Number':  return tFun(tVar('a'), tNumber);
    case 'Boolean': return tFun(tVar('a'), tBool);
    case 'Object':  return tFun(tVar('a'), tCon('Object', []));
    case 'Date': {
      const date = tCon('Date', []);
      return tUnion([
        tFun(tVoid, date),
        tFun(tString, date),
        tFun(tTuple([tSpread, tNumber]), date),
      ]);
    }
    case 'RegExp':
      return tFun(
        tTuple([tString, tUnion([tString, tUndefined])]),
        tCon('RegExp', []),
      );
    case 'Error':
    case 'TypeError':
    case 'RangeError':
    case 'ReferenceError':
    case 'SyntaxError':
      return tFun(tUnion([tString, tUndefined]), tCon(typeName, []));
    case 'Function':
      // Display fallback: `(..., String) -> Function`.  Call-site smart-infer
      // can intercept via `engine.builtinCtorKind` to parse the body string
      // argument and synthesise a more precise function type.
      return tFun(tTuple([tSpread, tString]), tCon('Function', []));
    default:
      return null;
  }
}

/**
 * Record a property-access error: stores `$error` as the node type, marks
 * the offset for hover suppression, emits a diagnostic, and returns the
 * error type so callers can `return` it directly.
 */
function recordPropertyError(
  engine: InferenceEngine,
  node: AstNode,
  message: string,
): Type {
  const errType = tCon(T_ERROR, []);
  engine.recordNodeType(node, errType);
  engine.unconstrainedPropAccesses.add(node.start);
  engine.addDiag(message, node);
  return errType;
}

/**
 * Record a suppressed property access (unconstrained TVar or wildcard).
 * Stores a fresh TVar as the node type and marks the offset for hover
 * suppression.
 */
function recordSuppressedProperty(
  engine: InferenceEngine,
  node: AstNode,
): Type {
  const suppressed = tVar();
  engine.recordNodeType(node, suppressed);
  engine.unconstrainedPropAccesses.add(node.start);
  return suppressed;
}

/**
 * Retry property accesses that were parked because their receiver was a bare
 * TVar at inference time.  For every entry whose receiver has SINCE been
 * pinned to a concrete type (record / data type / builtin), look the member
 * up again and quietly unify the placeholder result var with the real member
 * type — resolving e.g. `lens :: [b]` to `[Number]` once `[String]` arrived
 * as the curried data argument.  Entries whose receiver is still a TVar stay
 * parked (genuinely polymorphic parameters keep today's suppressed display).
 *
 * Called before a binding is generalized (so the resolved vars are not
 * spuriously quantified) and once more at end of inference as a catch-all.
 * Resolution is strictly additive: lookup misses and unification failures
 * are swallowed, preserving the previous silent behavior.
 */
const APPROXIMATING_CONS = new Set<string>([T_UNION, T_MERGE, T_PICKED, T_SPREAD_ARRAY]);

/** True if `t` contains a union, an overload set or a type operator. */
function hasApproximation(t: Type): boolean {
  return someType(t, (n) => n.tag === 'TCon' && APPROXIMATING_CONS.has(n.name));
}

export function flushDeferredMemberAccesses(engine: InferenceEngine): void {
  if (engine.deferredMemberAccesses.length === 0) return;
  const remaining: typeof engine.deferredMemberAccesses = [];
  for (const entry of engine.deferredMemberAccesses) {
    const obj = engine.maybeExpandAlias(engine.subst.apply(entry.objType));
    if (obj.tag === 'TVar') {
      remaining.push(entry);
      continue;
    }
    let memberType: Type | null = null;
    if (obj.tag === 'TRecord' && entry.propName in obj.fields) {
      memberType = obj.fields[entry.propName];
    } else if (obj.tag === 'TCon' && obj.name !== T_UNION && obj.name !== T_ERROR) {
      const method = lookupMethod(obj.name, entry.propName);
      if (method) {
        try {
          memberType = method.factory(obj.args);
        } catch {
          memberType = null;
        }
      }
    }
    if (memberType) {
      const member = engine.resolve(memberType);
      const demanded = engine.resolve(entry.resultType);
      try {
        engine.subst.mergeFrom(unify(member, demanded));
      } catch (e) {
        if (!(e instanceof UnificationError)) throw e;
        // The receiver is known now, so the member's real type must agree
        // with what the code already demanded of the placeholder (an
        // annotation, a later call): `// xs :: [String]` above
        // `map (s => s.length) (["a"])`.  Report a clash between plain types.
        // A union, an overload set or a type operator on either side usually
        // comes from an approximation elsewhere (a heterogeneous array
        // literal, `str.split`'s String/RegExp overloads, `Merge p q`), so
        // that clash stays silent, as before.
        if (!hasApproximation(member) && !hasApproximation(demanded)) {
          engine.unifyWithDiagnostic(member, demanded, entry.node);
        }
      }
      engine.unconstrainedPropAccesses.delete(entry.propStart);
    }
    // Concrete receiver — entry is consumed either way; a missing member
    // keeps the established silent (suppressed-hover) behavior.
  }
  engine.deferredMemberAccesses = remaining;
}
