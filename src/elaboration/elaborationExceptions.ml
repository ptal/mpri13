open Positions
open Name

exception UnboundIdentifier of position * name
exception UnboundTypeVariable of position * tname
exception UnboundClass of position * tname
exception UnboundInstance of position * Types.class_predicate
exception UnboundLabel of position * lname
exception MultipleLabels of position * lname
exception AlreadyDefinedClass of position * tname
exception AlreadyDefinedInstance of position * Types.class_predicate
exception InvalidTypeApplication of position
exception InvalidDataConstructorApplication of position
exception PatternsMustBindSameVariables of position
exception CannotElaborateDictionary of position * Types.t
exception NonLinearPattern of position
exception IncompatibleTypes of position * Types.t * Types.t
exception IncompatibleKinds of position * Types.kind * Types.kind
exception IllKindedType of position
exception RecordExpected of position * Types.t
exception ApplicationToNonFunctional of position
exception ValueRestriction of position
exception InvalidOverloading of position
exception OverloadingOfNonValueFormForbidden of position
exception InvalidNumberOfTypeAbstraction of position
exception TheseTwoClassesMustNotBeInTheSameContext of position * tname * tname
exception OverlappingInstances of position * tname
exception OnlyLetsCanIntroduceTypeAbstraction of position
exception SameNameInTypeAbstractionAndScheme of position
exception LabelAlreadyTaken of position * lname
exception LabelDoesNotBelong of position * lname * tname * tname
exception InvalidRecordInstantiation of position
exception OverloadedSymbolCannotBeBound of Positions.position * name
exception InvalidRecordConstruction of position
exception SuperclassesCannotBeRelated of position * tname * tname * tname
exception InstanceMemberNotInClass of position * tname * lname
exception MissingInstanceMember of position * tname * lname
exception AlreadyDefinedInstanceMember of position * lname
exception InstanceTypingContextCannotBeRelated of position * tname * tname * tname
exception InstanceTypingContextCannotBeEqual of position * tname * tname
exception CannotUseTypeRestrictedName of position * tname
exception CannotUseLabelRestrictedName of position * lname
exception CannotUseValueRestrictedName of position * name
exception UndeclaredInstance of position * tname * tname
exception InaccessibleDictionaryInTypingContext of position * tname * tname
exception ClassPredicateInValueForbidden of position * name
exception SameValueNameAsMemberName of position * name