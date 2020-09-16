import {
  RuleContext,
  RuleListener,
} from "@typescript-eslint/experimental-utils/dist/ts-eslint";
import {
  ESLintUtils,
  AST_NODE_TYPES,
} from "@typescript-eslint/experimental-utils";
import { get } from "total-functions";
import { Type, Symbol, IndexKind, Node } from "typescript";
import { assignableObjectPairs, TypeChecker } from "./common";

export type MessageId =
  | "errorStringCallExpression"
  | "errorStringAssignmentExpression"
  | "errorStringVariableDeclaration"
  | "errorStringArrowFunctionExpression"
  | "errorStringTSAsExpression"
  | "errorStringTSTypeAssertion";

export type TypePairArray = ReadonlyArray<{
  readonly destinationType: Type;
  readonly sourceType: Type;
}>;

export type Context = Readonly<RuleContext<MessageId, readonly []>>;

export type UnsafeIndexAssignmentFunc = (
  indexKind: IndexKind,
  destinationType: Type,
  sourceType: Type,
  checker: TypeChecker
) => boolean;

export type UnsafePropertyAssignmentFunc = (
  // eslint-disable-next-line @typescript-eslint/ban-types
  destinationProperty: Symbol,
  // eslint-disable-next-line @typescript-eslint/ban-types
  sourceProperty: Symbol | undefined,
  destinationType: Type,
  sourceType: Type,
  checker: TypeChecker
) => boolean;

export const createNoUnsafeAssignmentRule = (
  unsafePropertyAssignmentFunc: UnsafePropertyAssignmentFunc,
  unsafeIndexAssignmentFunc: UnsafeIndexAssignmentFunc
  // eslint-disable-next-line sonarjs/cognitive-complexity
) => (context: Context): RuleListener => {
  const parserServices = ESLintUtils.getParserServices(context);
  const checker: TypeChecker = parserServices.program.getTypeChecker();

  const isUnsafeIndexAssignment = (
    indexKind: IndexKind,
    destinationNode: Node,
    sourceNode: Node,
    destinationType: Type,
    sourceType: Type,
    checker: TypeChecker,
    seenTypes: TypePairArray
  ): boolean => {
    const isUnsafe = unsafeIndexAssignmentFunc(
      indexKind,
      destinationType,
      sourceType,
      checker
    );

    const destinationIndexType =
      indexKind === IndexKind.Number
        ? destinationType.getNumberIndexType()
        : destinationType.getStringIndexType();
    const sourceIndexType =
      indexKind === IndexKind.Number
        ? sourceType.getNumberIndexType()
        : sourceType.getStringIndexType();

    // This is unsafe if...
    return (
      // this particular rule considers the index assignment unsafe, or
      isUnsafe ||
      // the index types are considered unsafe themselves (recursively).
      (destinationIndexType !== undefined &&
        sourceIndexType !== undefined &&
        isUnsafeAssignment(
          destinationNode,
          sourceNode,
          destinationIndexType,
          sourceIndexType,
          checker,
          seenTypes
        ))
    );
  };

  const isUnsafePropertyAssignmentRec = (
    destinationNode: Node,
    sourceNode: Node,
    // eslint-disable-next-line @typescript-eslint/ban-types
    destinationProperty: Symbol,
    // eslint-disable-next-line @typescript-eslint/ban-types
    sourceProperty: Symbol,
    checker: TypeChecker,
    seenTypes: TypePairArray
  ): boolean => {
    const destinationPropertyType = checker.getTypeOfSymbolAtLocation(
      destinationProperty,
      destinationNode
    );
    const sourcePropertyType = checker.getTypeOfSymbolAtLocation(
      sourceProperty,
      sourceNode
    );

    return isUnsafeAssignment(
      destinationNode,
      sourceNode,
      destinationPropertyType,
      sourcePropertyType,
      checker,
      seenTypes
    );
  };

  const isUnsafePropertyAssignment = (
    destinationNode: Node,
    sourceNode: Node,
    destinationType: Type,
    sourceType: Type,
    checker: TypeChecker,
    seenTypes: TypePairArray
  ): boolean => {
    return destinationType.getProperties().some((destinationProperty) => {
      const sourceProperty = sourceType.getProperty(destinationProperty.name);

      const isUnsafe = unsafePropertyAssignmentFunc(
        destinationProperty,
        sourceProperty,
        destinationType,
        sourceType,
        checker
      );

      // eslint-disable-next-line functional/no-conditional-statement
      if (isUnsafe) {
        return true;
      }

      // eslint-disable-next-line functional/no-conditional-statement
      if (sourceProperty === undefined) {
        return false;
      }

      const nextSeenTypes: TypePairArray = seenTypes.concat({
        destinationType,
        sourceType,
      });

      return isUnsafePropertyAssignmentRec(
        destinationNode,
        sourceNode,
        destinationProperty,
        sourceProperty,
        checker,
        nextSeenTypes
      );
    });
  };

  const isUnsafeAssignment = (
    destinationNode: Node,
    sourceNode: Node,
    rawDestinationType: Type,
    rawSourceType: Type,
    checker: TypeChecker,
    seenTypes: TypePairArray = []
  ): boolean => {
    const typePairs = assignableObjectPairs(
      rawDestinationType,
      rawSourceType,
      checker
    );

    return typePairs.some(({ sourceType, destinationType }) => {
      const nextSeenTypes: TypePairArray = seenTypes.concat({
        destinationType,
        sourceType,
      });

      // TODO this needs to compare function return types
      // This is an unsafe assignment if...
      return (
        // we're not in an infinitely recursive type,
        seenTypes.every(
          (t) =>
            t.destinationType !== destinationType && t.sourceType !== sourceType
        ) &&
        // and the types we're assigning from and to are different,
        // TODO this seems to be required to prevent a hang in https://github.com/oaf-project/oaf-react-router
        // Need to work out why and formulate a test to reproduce
        destinationType !== sourceType &&
        // and we're either:
        // unsafe string index assignment, or
        (isUnsafeIndexAssignment(
          IndexKind.String,
          destinationNode,
          sourceNode,
          destinationType,
          sourceType,
          checker,
          nextSeenTypes
        ) ||
          // unsafe number index assignment, or
          isUnsafeIndexAssignment(
            IndexKind.Number,
            destinationNode,
            sourceNode,
            destinationType,
            sourceType,
            checker,
            nextSeenTypes
          ) ||
          // unsafe property assignment.
          isUnsafePropertyAssignment(
            destinationNode,
            sourceNode,
            destinationType,
            sourceType,
            checker,
            nextSeenTypes
          ))
      );
    });
  };

  return {
    // eslint-disable-next-line functional/no-return-void
    TSTypeAssertion: (node): void => {
      // eslint-disable-next-line functional/no-conditional-statement
      if (
        node.typeAnnotation.type === AST_NODE_TYPES.TSTypeReference &&
        node.typeAnnotation.typeName.type === AST_NODE_TYPES.Identifier &&
        node.typeAnnotation.typeName.name === "const"
      ) {
        // Always allow `as const`.
        return;
      }

      const destinationNode = parserServices.esTreeNodeToTSNodeMap.get(node);
      const destinationType = checker.getTypeAtLocation(destinationNode);
      const sourceNode = destinationNode.expression;
      const sourceType = checker.getTypeAtLocation(sourceNode);

      // eslint-disable-next-line functional/no-conditional-statement
      if (
        isUnsafeAssignment(
          destinationNode,
          sourceNode,
          destinationType,
          sourceType,
          checker
        )
      ) {
        // eslint-disable-next-line functional/no-expression-statement
        context.report({
          node: node,
          messageId: "errorStringTSTypeAssertion",
        });
      }
    },
    // eslint-disable-next-line functional/no-return-void
    TSAsExpression: (node): void => {
      // eslint-disable-next-line functional/no-conditional-statement
      if (
        node.typeAnnotation.type === AST_NODE_TYPES.TSTypeReference &&
        node.typeAnnotation.typeName.type === AST_NODE_TYPES.Identifier &&
        node.typeAnnotation.typeName.name === "const"
      ) {
        // Always allow `as const`.
        return;
      }

      const destinationNode = parserServices.esTreeNodeToTSNodeMap.get(node);
      const destinationType = checker.getTypeAtLocation(destinationNode);
      const sourceNode = destinationNode.expression;
      const sourceType = checker.getTypeAtLocation(sourceNode);

      // eslint-disable-next-line functional/no-conditional-statement
      if (
        isUnsafeAssignment(
          destinationNode,
          sourceNode,
          destinationType,
          sourceType,
          checker
        )
      ) {
        // eslint-disable-next-line functional/no-expression-statement
        context.report({
          node: node,
          messageId: "errorStringTSAsExpression",
        });
      }
    },
    // eslint-disable-next-line functional/no-return-void
    VariableDeclaration: (node): void => {
      // eslint-disable-next-line functional/no-expression-statement
      node.declarations.forEach((declaration) => {
        // eslint-disable-next-line functional/no-conditional-statement
        if (
          declaration.id.type === AST_NODE_TYPES.Identifier &&
          declaration.id.typeAnnotation === undefined
        ) {
          // If there is no type annotation then there's no risk of unsafe assignment.
          return;
        }

        // eslint-disable-next-line functional/no-conditional-statement
        if (declaration.init === null) {
          // If there is no type annotation then there's no risk of unsafe assignment.
          return;
        }

        const leftTsNode = parserServices.esTreeNodeToTSNodeMap.get(
          declaration.id
        );
        const rightTsNode = parserServices.esTreeNodeToTSNodeMap.get(
          declaration.init
        );

        const leftType = checker.getTypeAtLocation(leftTsNode);
        const rightType = checker.getTypeAtLocation(rightTsNode);

        // eslint-disable-next-line functional/no-conditional-statement
        if (
          isUnsafeAssignment(
            leftTsNode,
            rightTsNode,
            leftType,
            rightType,
            checker
          )
        ) {
          // eslint-disable-next-line functional/no-expression-statement
          context.report({
            node: node,
            messageId: "errorStringVariableDeclaration",
          });
        }
      });
    },
    // eslint-disable-next-line functional/no-return-void
    AssignmentExpression: (node): void => {
      const leftTsNode = parserServices.esTreeNodeToTSNodeMap.get(node.left);
      const rightTsNode = parserServices.esTreeNodeToTSNodeMap.get(node.right);

      const leftType = checker.getTypeAtLocation(leftTsNode);
      const rightType = checker.getTypeAtLocation(rightTsNode);

      // eslint-disable-next-line functional/no-conditional-statement
      if (
        isUnsafeAssignment(
          leftTsNode,
          rightTsNode,
          leftType,
          rightType,
          checker
        )
      ) {
        // eslint-disable-next-line functional/no-expression-statement
        context.report({
          node: node,
          messageId: "errorStringAssignmentExpression",
        });
      }
    },
    // eslint-disable-next-line functional/no-return-void
    ReturnStatement: (node): void => {
      const tsNode = parserServices.esTreeNodeToTSNodeMap.get(node);

      // eslint-disable-next-line functional/no-conditional-statement
      if (tsNode.expression === undefined) {
        return;
      }

      const destinationType = checker.getContextualType(tsNode.expression);
      const sourceType = checker.getTypeAtLocation(tsNode.expression);

      // eslint-disable-next-line functional/no-conditional-statement
      if (
        destinationType !== undefined &&
        isUnsafeAssignment(
          tsNode.expression,
          tsNode.expression,
          destinationType,
          sourceType,
          checker
        )
      ) {
        // eslint-disable-next-line functional/no-expression-statement
        context.report({
          node: node,
          messageId: "errorStringArrowFunctionExpression",
        });
      }
    },
    // TODO: YieldExpression?
    // eslint-disable-next-line functional/no-return-void
    ArrowFunctionExpression: (node): void => {
      // eslint-disable-next-line functional/no-conditional-statement
      if (node.returnType === undefined) {
        return;
      }
      const destinationNode = parserServices.esTreeNodeToTSNodeMap.get(
        node.returnType.typeAnnotation
      );
      const destinationType = checker.getTypeAtLocation(destinationNode);
      const sourceNode = parserServices.esTreeNodeToTSNodeMap.get(node.body);
      const sourceType = checker.getTypeAtLocation(sourceNode);

      // eslint-disable-next-line functional/no-conditional-statement
      if (
        isUnsafeAssignment(
          destinationNode,
          sourceNode,
          destinationType,
          sourceType,
          checker
        )
      ) {
        // eslint-disable-next-line functional/no-expression-statement
        context.report({
          node: node.body,
          messageId: "errorStringArrowFunctionExpression",
        });
      }
    },
    // eslint-disable-next-line functional/no-return-void
    CallExpression: (node): void => {
      const tsNode = parserServices.esTreeNodeToTSNodeMap.get(node);

      // eslint-disable-next-line functional/no-expression-statement
      tsNode.arguments.forEach((argument, i) => {
        const argumentType = checker.getTypeAtLocation(argument);
        const paramType = checker.getContextualType(argument);

        // eslint-disable-next-line functional/no-conditional-statement
        if (
          paramType !== undefined &&
          isUnsafeAssignment(
            argument,
            argument,
            paramType,
            argumentType,
            checker
          )
        ) {
          // eslint-disable-next-line functional/no-expression-statement
          context.report({
            node: get(node.arguments, i) ?? node,
            messageId: "errorStringCallExpression",
          });
        }
      });
    },
  };
};