/*
 * Copyright 2012 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.codehaus.groovy.grails.transaction.transform

import static org.codehaus.groovy.grails.compiler.injection.GrailsASTUtils.*
import grails.transaction.Transactional
import groovy.transform.CompileStatic

import java.lang.reflect.Modifier

import org.codehaus.groovy.ast.*
import org.codehaus.groovy.ast.expr.*
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.CatchStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.ThrowStatement
import org.codehaus.groovy.ast.stmt.TryCatchStatement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.grails.compiler.injection.GrailsASTUtils
import org.codehaus.groovy.grails.compiler.injection.GrailsArtefactClassInjector
import org.codehaus.groovy.grails.orm.support.TransactionManagerAware
import org.codehaus.groovy.syntax.Token
import org.codehaus.groovy.syntax.Types
import org.codehaus.groovy.transform.ASTTransformation
import org.codehaus.groovy.transform.GroovyASTTransformation
import org.springframework.transaction.PlatformTransactionManager
import org.springframework.transaction.TransactionStatus
import org.springframework.transaction.annotation.Isolation
import org.springframework.transaction.annotation.Propagation
import org.springframework.transaction.support.TransactionCallback
import org.springframework.transaction.support.TransactionTemplate

/**
 * This AST transform reads the {@link grails.transaction.Transactional} annotation and transforms method calls by
 * wrapping the body of the method in an execution of {@link org.springframework.transaction.support.TransactionTemplate#execute(org.springframework.transaction.support.TransactionCallback)}.
 *
 *
 * @author Graeme Rocher
 * @since 2.3
 */
@CompileStatic
@GroovyASTTransformation(phase = CompilePhase.CANONICALIZATION)
class TransactionalTransform implements ASTTransformation{
    public static final ClassNode MY_TYPE = new ClassNode(Transactional).getPlainNodeReference();
    private static final String PROPERTY_TRANSACTION_MANAGER = "transactionManager"
    private static final String METHOD_EXECUTE = "execute"

    @Override
    void visit(ASTNode[] astNodes, SourceUnit source) {
        if (!(astNodes[0] instanceof AnnotationNode) || !(astNodes[1] instanceof AnnotatedNode)) {
            throw new RuntimeException('Internal error: wrong types: $node.class / $parent.class')
        }

        AnnotatedNode parent = (AnnotatedNode) astNodes[1];
        AnnotationNode annotationNode = (AnnotationNode) astNodes[0];
        if (!MY_TYPE.equals(annotationNode.getClassNode())) {
            return;
        }

        if (parent instanceof MethodNode) {
            MethodNode methodNode = (MethodNode)parent


            final declaringClassNode = methodNode.getDeclaringClass()

            weaveTransactionManagerAware(declaringClassNode)
            weaveTransactionalMethod(declaringClassNode, annotationNode, methodNode)
        }
        else if (parent instanceof ClassNode) {
            weaveTransactionalBehavior(parent, annotationNode)
        }

    }

    public void weaveTransactionalBehavior(ClassNode classNode, AnnotationNode annotationNode) {
        weaveTransactionManagerAware(classNode)

        ClassNode controllerMethodAnn = getAnnotationClassNode("grails.web.controllers.ControllerMethod")

        List<MethodNode> deferredMethods = new ArrayList<MethodNode>();
        
        List<MethodNode> methods = new ArrayList<MethodNode>(classNode.getMethods());
        
        for (MethodNode md in methods) {
            if (Modifier.isPublic(md.modifiers) && !Modifier.isAbstract(md.modifiers)) {
                if (md.getAnnotations(MY_TYPE)) continue

                if (controllerMethodAnn && md.getAnnotations(controllerMethodAnn)) continue
                weaveTransactionalMethod(classNode, annotationNode, md);
            }
        }
    }

    ClassNode getAnnotationClassNode(String annotationName) {
        try {
            final classLoader = Thread.currentThread().contextClassLoader
            final clazz = classLoader.loadClass(annotationName)
            return new ClassNode(clazz)
        } catch (e) {
            return null
        }
    }

    protected void weaveTransactionalMethod(ClassNode classNode, AnnotationNode annotationNode, MethodNode methodNode) {
        String renamedMethodName = '$tt__' + methodNode.getName()
        final transactionStatusParameter = new Parameter(ClassHelper.make(TransactionStatus).getPlainNodeReference(), "transactionStatus")
        def newParameters = copyParameters(((methodNode.getParameters() as List) + [transactionStatusParameter]) as Parameter[]) 
        
        MethodNode renamedMethodNode = new MethodNode(
                renamedMethodName,
                Modifier.PROTECTED, methodNode.getReturnType(),
                newParameters,
                GrailsArtefactClassInjector.EMPTY_CLASS_ARRAY,
                methodNode.code
                );
        classNode.addMethod(renamedMethodNode);
        
        BlockStatement methodBody = new BlockStatement()

        final constructorArgs = new ArgumentListExpression()
        constructorArgs.addExpression(new VariableExpression(PROPERTY_TRANSACTION_MANAGER, ClassHelper.make(PlatformTransactionManager)));
        final transactionTemplateClassNode = ClassHelper.make(TransactionTemplate).getPlainNodeReference()
        final transactionTemplateVar = new VariableExpression('$transactionTemplate', transactionTemplateClassNode)
        methodBody.addStatement(
            new ExpressionStatement(
                new DeclarationExpression(
                    transactionTemplateVar,
                    GrailsASTUtils.ASSIGNMENT_OPERATOR,
                    new ConstructorCallExpression(transactionTemplateClassNode, constructorArgs)
                )
            )
        )

        final members = annotationNode.getMembers()
        members.each { String name, Expression expr ->

            if (name == 'isolation') {
                name = 'isolationLevel'
                expr = applyDefaultMethodTarget(new MethodCallExpression(expr, "value", new ArgumentListExpression()), Isolation.class);
            } else if (name == 'propagation') {
                name = 'propagationBehavior'
                expr = applyDefaultMethodTarget(new MethodCallExpression(expr, "value", new ArgumentListExpression()), Propagation.class)
            }

            methodBody.addStatement(
                new ExpressionStatement(
                    buildSetPropertyExpression(transactionTemplateVar, name, transactionTemplateClassNode, expr)
                )
            )
        }
        
        final variableScope = new VariableScope()
        for (Parameter p in methodNode.parameters) {
            p.setClosureSharedVariable(true);
            variableScope.putReferencedLocalVariable(p);
        }
        final originalMethodCall = new MethodCallExpression(new VariableExpression("this"), renamedMethodName, new ArgumentListExpression(renamedMethodNode.parameters))
        originalMethodCall.setImplicitThis(false)
        originalMethodCall.setMethodTarget(renamedMethodNode)
        final tryCatchStatement = new TryCatchStatement(new ExpressionStatement(originalMethodCall), new EmptyStatement())

        final runtimeExceptionThrowStatement = new ThrowStatement(new VariableExpression('$ex'))
        tryCatchStatement.addCatch(new CatchStatement(new Parameter(new ClassNode(RuntimeException.class), '$ex'), runtimeExceptionThrowStatement))

        final throwableHolderClassNode = ClassHelper.make(ThrowableHolder).getPlainNodeReference()
        final throwableHolderConstructorArgs = new ArgumentListExpression()
        throwableHolderConstructorArgs.addExpression(new VariableExpression('$ex'))
        final throwableHolderReturnStatement = new ReturnStatement(new ConstructorCallExpression(throwableHolderClassNode, throwableHolderConstructorArgs))
        tryCatchStatement.addCatch(new CatchStatement(new Parameter(new ClassNode(Exception.class), '$ex'), throwableHolderReturnStatement))

        final executeMethodParameterTypes = [transactionStatusParameter] as Parameter[]
        final callCallExpression = new ClosureExpression(executeMethodParameterTypes, tryCatchStatement)


        callCallExpression.setVariableScope(variableScope)
        final castExpression = new CastExpression(ClassHelper.make(TransactionCallback).getPlainNodeReference(),
            callCallExpression
        )
        castExpression.coerce = true
        final methodArgs = new ArgumentListExpression(castExpression)

        final transactionTemplateResultVar = new VariableExpression('$transactionTemplateExecuteResult')
        final executeMethodCallExpression = applyDefaultMethodTarget(new MethodCallExpression(transactionTemplateVar, METHOD_EXECUTE, methodArgs), transactionTemplateClassNode)
        methodBody.addStatement(new ExpressionStatement(
            new DeclarationExpression(
                transactionTemplateResultVar,
                GrailsASTUtils.ASSIGNMENT_OPERATOR,
                executeMethodCallExpression
            )
        ))

        final instanceOfThrowableHolderExpression = new BooleanExpression(new BinaryExpression(
            transactionTemplateResultVar, Token.newSymbol(Types.KEYWORD_INSTANCEOF, 0, 0), new ClassExpression(throwableHolderClassNode)
        ))
        final throwableHolderThrowStatement = new ThrowStatement(applyDefaultMethodTarget(new MethodCallExpression(transactionTemplateResultVar, "getThrowable", GrailsASTUtils.ZERO_ARGUMENTS), ThrowableHolder.class));
        methodBody.addStatement(new IfStatement(instanceOfThrowableHolderExpression, throwableHolderThrowStatement, new EmptyStatement()))
        
        if(methodNode.getReturnType() != ClassHelper.VOID_TYPE) {
            methodBody.addStatement(new ReturnStatement(new CastExpression(methodNode.getReturnType(), transactionTemplateResultVar)))
        }
        methodNode.setCode(methodBody)
    }

    protected void weaveTransactionManagerAware(ClassNode declaringClassNode) {
        ClassNode transactionManagerAwareInterface = ClassHelper.make(TransactionManagerAware).getPlainNodeReference()

        if (!GrailsASTUtils.findInterface(declaringClassNode, transactionManagerAwareInterface)) {
            declaringClassNode.addInterface(transactionManagerAwareInterface)

            //add the transactionManager property
            final transactionManagerProperty = declaringClassNode.getProperty(PROPERTY_TRANSACTION_MANAGER)
            if (!transactionManagerProperty) {
                declaringClassNode.addProperty(PROPERTY_TRANSACTION_MANAGER, Modifier.PUBLIC, ClassHelper.make(PlatformTransactionManager).getPlainNodeReference(), null, null, null);
            }

        }
    }
}
