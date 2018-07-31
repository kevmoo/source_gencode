import 'package:analyzer/dart/element/element.dart';
import 'package:analyzer/dart/element/type.dart';

// ignore: implementation_imports
import 'package:analyzer/src/dart/resolver/inheritance_manager.dart'
    show InheritanceManager;

import 'package:build/build.dart';
import 'package:source_gen/source_gen.dart';

export 'src/escape_dart_string.dart';
export 'src/type_arguments_of.dart';

bool isEnum(DartType targetType) =>
    targetType is InterfaceType && targetType.element.isEnum;

/// [availableConstructorParameters] is checked to see if it is available. If
/// [availableConstructorParameters] does not contain the parameter name,
/// an [UnsupportedError] is thrown.
///
/// To improve the error details, [unavailableReasons] is checked for the
/// unavailable constructor parameter. If the value is not `null`, it is
/// included in the [UnsupportedError] message.
///
/// [writeableFields] are also populated, but only if they have not already
/// been defined by a constructor parameter with the same name.
ConstructorData writeConstructorInvocation(
    ClassElement classElement,
    Iterable<String> availableConstructorParameters,
    Iterable<String> writeableFields,
    Map<String, String> unavailableReasons,
    String deserializeForField(String paramOrFieldName,
        {ParameterElement ctorParam})) {
  var className = classElement.name;

  var ctor = classElement.unnamedConstructor;
  if (ctor == null) {
    // TODO(kevmoo): support using another ctor - dart-lang/json_serializable#50
    throw new UnsupportedError(
        'The class `$className` has no default constructor.');
  }

  var usedCtorParamsAndFields = new Set<String>();
  var constructorArguments = <ParameterElement>[];
  var namedConstructorArguments = <ParameterElement>[];

  for (var arg in ctor.parameters) {
    if (!availableConstructorParameters.contains(arg.name)) {
      if (arg.isNotOptional) {
        var msg = 'Cannot populate the required constructor '
            'argument: ${arg.name}.';

        var additionalInfo = unavailableReasons[arg.name];

        if (additionalInfo != null) {
          msg = '$msg $additionalInfo';
        }

        throw new UnsupportedError(msg);
      }

      continue;
    }

    // TODO: validate that the types match!
    if (arg.isNamed) {
      namedConstructorArguments.add(arg);
    } else {
      constructorArguments.add(arg);
    }
    usedCtorParamsAndFields.add(arg.name);
  }

  warnUndefinedElements(
      constructorArguments.followedBy(namedConstructorArguments));

  // fields that aren't already set by the constructor and that aren't final
  var remainingFieldsForInvocationBody =
      writeableFields.toSet().difference(usedCtorParamsAndFields);

  var buffer = new StringBuffer();
  buffer.write('new $className${genericClassArguments(classElement, false)}(');
  if (constructorArguments.isNotEmpty) {
    buffer.writeln();
    buffer.writeAll(constructorArguments.map((paramElement) {
      var content =
          deserializeForField(paramElement.name, ctorParam: paramElement);
      return '      $content';
    }), ',\n');
    if (namedConstructorArguments.isNotEmpty) {
      buffer.write(',');
    }
  }
  if (namedConstructorArguments.isNotEmpty) {
    buffer.writeln();
    buffer.writeAll(namedConstructorArguments.map((paramElement) {
      var value =
          deserializeForField(paramElement.name, ctorParam: paramElement);
      return '      ${paramElement.name}: $value';
    }), ',\n');
  }

  buffer.write(')');

  usedCtorParamsAndFields.addAll(remainingFieldsForInvocationBody);

  return new ConstructorData(buffer.toString(),
      remainingFieldsForInvocationBody, usedCtorParamsAndFields);
}

class ConstructorData {
  final String content;
  final Set<String> fieldsToSet;
  final Set<String> usedCtorParamsAndFields;
  ConstructorData(this.content, this.fieldsToSet, this.usedCtorParamsAndFields);
}

/// Returns a [String] representing the type arguments that exist on
/// [element].
///
/// If [withConstraints] is `null` or if [element] has no type arguments, an
/// empty [String] is returned.
///
/// If [withConstraints] is true, any type constraints that exist on [element]
/// are included.
///
/// For example, for class `class Sample<T as num, S>{...}`
///
/// For [withConstraints] = `false`:
///
/// ```
/// "<T, S>"
/// ```
///
/// For [withConstraints] = `true`:
///
/// ```
/// "<T as num, S>"
/// ```
String genericClassArguments(ClassElement element, bool withConstraints) {
  if (withConstraints == null || element.typeParameters.isEmpty) {
    return '';
  }
  var values = element.typeParameters
      .map((t) => withConstraints ? t.toString() : t.name)
      .join(', ');
  return '<$values>';
}

void warnUndefinedElements(Iterable<VariableElement> elements) {
  for (var element in elements.where((fe) => fe.type.isUndefined)) {
    var span = spanForElement(element);
    log.warning('''
This element has an undefined type. It may causes issues when generated code.
${span.start.toolString}
${span.highlight()}''');
  }
}

/// Returns a [Set] of all instance [FieldElement] items for [element] and
/// super classes, sorted first by their location in the inheritance hierarchy
/// (super first) and then by their location in the source file.
Set<FieldElement> createSortedFieldSet(ClassElement element) {
  // Get all of the fields that need to be assigned
  // TODO: support overriding the field set with an annotation option
  var fieldsList = element.fields.where((e) => !e.isStatic).toList();

  var manager = new InheritanceManager(element.library);

  for (var v in manager.getMembersInheritedFromClasses(element).values) {
    assert(v is! FieldElement);
    if (_dartCoreObjectChecker.isExactly(v.enclosingElement)) {
      continue;
    }

    if (v is PropertyAccessorElement && v.variable is FieldElement) {
      fieldsList.add(v.variable as FieldElement);
    }
  }

  warnUndefinedElements(fieldsList);

  // Sort these in the order in which they appear in the class
  // Sadly, `classElement.fields` puts properties after fields
  fieldsList.sort(_sortByLocation);

  return fieldsList.toSet();
}

int _sortByLocation(FieldElement a, FieldElement b) {
  var checkerA = new TypeChecker.fromStatic(a.enclosingElement.type);

  if (!checkerA.isExactly(b.enclosingElement)) {
    // in this case, you want to prioritize the enclosingElement that is more
    // "super".

    if (checkerA.isSuperOf(b.enclosingElement)) {
      return -1;
    }

    var checkerB = new TypeChecker.fromStatic(b.enclosingElement.type);

    if (checkerB.isSuperOf(a.enclosingElement)) {
      return 1;
    }
  }

  /// Returns the offset of given field/property in its source file – with a
  /// preference for the getter if it's defined.
  int _offsetFor(FieldElement e) {
    if (e.getter != null && e.getter.nameOffset != e.nameOffset) {
      assert(e.nameOffset == -1);
      return e.getter.nameOffset;
    }
    return e.nameOffset;
  }

  return _offsetFor(a).compareTo(_offsetFor(b));
}

final _dartCoreObjectChecker = const TypeChecker.fromRuntime(Object);
