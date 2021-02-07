package main.visitor.codeGenerator;
import com.sun.jdi.event.StepEvent;
import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.operators.BinaryOperator;
import main.ast.nodes.expression.operators.UnaryOperator;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;
import main.ast.nodes.statement.*;
import main.ast.nodes.statement.loop.BreakStmt;
import main.ast.nodes.statement.loop.ContinueStmt;
import main.ast.nodes.statement.loop.ForStmt;
import main.ast.nodes.statement.loop.ForeachStmt;
import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.list.ListNameType;
import main.ast.types.list.ListType;
import main.ast.types.single.BoolType;
import main.ast.types.single.ClassType;
import main.ast.types.single.IntType;
import main.ast.types.single.StringType;
import main.symbolTable.SymbolTable;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.ClassSymbolTableItem;
import main.symbolTable.items.FieldSymbolTableItem;
import main.symbolTable.items.MethodSymbolTableItem;
import main.symbolTable.items.SymbolTableItem;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;
import main.visitor.typeChecker.ExpressionTypeChecker;
import org.antlr.v4.misc.EscapeSequenceParsing;
import parsers.SophiaParser;
import java.awt.*;
import java.awt.desktop.SystemEventListener;
import java.awt.image.AreaAveragingScaleFilter;
import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class CodeGenerator extends Visitor<String> {
    ExpressionTypeChecker expressionTypeChecker;
    Graph<String> classHierarchy;
    private String outputPath;
    private FileWriter currentFile;
    private ClassDeclaration currentClass;
    private MethodDeclaration currentMethod;
    private Stack<String> startLoopLabel = new Stack<>();
    private Stack<String> endLoopLabel = new Stack<>();
    private Integer label_seed = 0;
    private int last_slot = 0;

    public CodeGenerator(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.expressionTypeChecker = new ExpressionTypeChecker(classHierarchy);
        this.prepareOutputFolder();
    }

    private void prepareOutputFolder() {
        this.outputPath = "output/";
        String jasminPath = "utilities/jarFiles/jasmin.jar";
        String listClassPath = "utilities/codeGenerationUtilityClasses/List.j";
        String fptrClassPath = "utilities/codeGenerationUtilityClasses/Fptr.j";
        try{
            File directory = new File(this.outputPath);
            File[] files = directory.listFiles();
            if(files != null)
                for (File file : files)
                    file.delete();
            directory.mkdir();
        }
        catch(SecurityException e) { }
        copyFile(jasminPath, this.outputPath + "jasmin.jar");
        copyFile(listClassPath, this.outputPath + "List.j");
        copyFile(fptrClassPath, this.outputPath + "Fptr.j");
    }

    private void copyFile(String toBeCopied, String toBePasted) {
        try {
            File readingFile = new File(toBeCopied);
            File writingFile = new File(toBePasted);
            InputStream readingFileStream = new FileInputStream(readingFile);
            OutputStream writingFileStream = new FileOutputStream(writingFile);
            byte[] buffer = new byte[1024];
            int readLength;
            while ((readLength = readingFileStream.read(buffer)) > 0)
                writingFileStream.write(buffer, 0, readLength);
            readingFileStream.close();
            writingFileStream.close();
        } catch (IOException e) { }
    }

    private void createFile(String name) {
        try {
            String path = this.outputPath + name + ".j";
            File file = new File(path);
            file.createNewFile();
            FileWriter fileWriter = new FileWriter(path);
            this.currentFile = fileWriter;
        } catch (IOException e) {}
    }

    private void addCommand(String command) {
        try {
            command = String.join("\n\t\t", command.split("\n"));
            if(command.startsWith("Label_"))
                this.currentFile.write("\t" + command + "\n");
            else if(command.startsWith(".") || command.startsWith(";"))
                this.currentFile.write(command + "\n");
            else
                this.currentFile.write("\t\t" + command + "\n");
            this.currentFile.flush();
        } catch (IOException e) {}
    }

    private String makeTypeSignature(Type t) {
        if(t instanceof IntType)
            return "Ljava/lang/Integer;";
        else if(t instanceof StringType)
            return "Ljava/lang/String;";
        else if(t instanceof BoolType)
            return "Ljava/lang/Boolean;";
        else if(t instanceof ListType)
            return "LList;";
        else if(t instanceof FptrType)
            return "LFptr;";
        else if(t instanceof NullType)
            return "V";
        else if(t instanceof ClassType)
            return "L" + ((ClassType)t).getClassName().getName() + ";";
        return null;
    }

    private String init(Type t) {
        String command = "";
        if (t instanceof StringType)
            command += "ldc \"\"\n";
        else if (t instanceof IntType) {
            command += "ldc 0\n";
            command += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
        } else if (t instanceof BoolType) {
            command += "ldc 0\n";
            command += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
        } else if (t instanceof ClassType || t instanceof FptrType)
            command += "aconst_null\n";
        else if (t instanceof ListType) {
            command += "new List\ndup\nnew java/util/ArrayList\ndup\ninvokespecial java/util/ArrayList/<init>()V\n";
            for (ListNameType e : ((ListType) t).getElementsTypes()) {
                command += "dup\n";
                command += init(e.getType());
                command += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\npop\n";
            }
            command += "invokespecial List/<init>(Ljava/util/ArrayList;)V\n";
        }
        return command;
    }

    private String generateLabel(){
        label_seed += 1;
        return "Label_" + label_seed.toString();
    }

    private String checkCast(Type t){
        if(t instanceof IntType)
            return "checkcast java/lang/Integer\n";
        else if(t instanceof  BoolType)
            return "checkcast java/lang/Boolean\n";
        else if(t instanceof StringType)
            return "checkcast java/lang/String\n";
        else if(t instanceof ListType)
            return "checkcast List\n";
        else if(t instanceof FptrType)
            return "checkcast Fptr\n";
        else if(t instanceof ClassType)
            return "checkcast " + ((ClassType) t).getClassName().getName() + "\n";
        else
            return "";
    }

    private void addDefaultConstructor() {
        String command = ".method public <init>()V\n.limit stack 128\n.limit locals 128\naload_0\ninvokespecial ";
        if(this.currentClass.getParentClassName() == null)
            command += "java/lang/Object/<init>()V\n";
        else
            command += currentClass.getParentClassName().getName() + "/<init>()V\n";
        for(FieldDeclaration field: currentClass.getFields()){
            command += "aload_0\n";
            Type t = field.getVarDeclaration().getType();
            command += init(t);
            command += "putfield " + currentClass.getClassName().getName() + "/" + field.getVarDeclaration().getVarName().getName() + " " + makeTypeSignature(t) + "\n";
        }
        command += "return\n.end method";
        addCommand(command);
    }

    private void addStaticMainMethod() {
        String command = ".method public static main([Ljava/lang/String;)V\n.limit stack 128\n.limit locals 128\nnew Main\ninvokespecial Main/<init>()V\nreturn\n.end method";
        addCommand(command);
    }

    private int slotOf(String identifier) {
        int i = 1;
        for(VarDeclaration var: currentMethod.getArgs()){
            if(var.getVarName().getName().equals(identifier))
                return i;
            i++;
        }
        for(VarDeclaration var: currentMethod.getLocalVars()){
            if(var.getVarName().getName().equals(identifier))
                return i;
            i++;
        }
        if(identifier.equals("")){
            if(last_slot == 0)
                last_slot = i;
            else
                last_slot++;
        }
        return last_slot;
    }

    @Override
    public String visit(Program program) {
        for(ClassDeclaration c: program.getClasses()){
            currentClass = c;
            expressionTypeChecker.setCurrentClass(c);
            c.accept(this);
        }
        return null;
    }

    @Override
    public String visit(ClassDeclaration classDeclaration) {
        createFile(classDeclaration.getClassName().getName());
        addCommand(".class public " + classDeclaration.getClassName().getName());
        if(classDeclaration.getParentClassName() == null)
            addCommand(".super java/lang/Object");
        else
            addCommand(".super " + classDeclaration.getParentClassName().getName());
        for(FieldDeclaration field: classDeclaration.getFields()){
            String command = field.accept(this);
            addCommand(command);
        }
        if(classDeclaration.getConstructor() == null)
            addDefaultConstructor();
        else{
            this.last_slot = 0;
            currentMethod = classDeclaration.getConstructor();
            expressionTypeChecker.setCurrentMethod(currentMethod);
            classDeclaration.getConstructor().accept(this);
        }
        for(MethodDeclaration method: classDeclaration.getMethods()) {
            this.last_slot = 0;
            currentMethod = method;
            expressionTypeChecker.setCurrentMethod(currentMethod);
            method.accept(this);
        }
        return null;
    }

    @Override
    public String visit(ConstructorDeclaration constructorDeclaration) {
        if(constructorDeclaration.getArgs().size() > 0)
            addDefaultConstructor();
        if(currentClass.getClassName().getName().equals("Main"))
            addStaticMainMethod();
        this.visit((MethodDeclaration) constructorDeclaration);
        return null;
    }

    @Override
    public String visit(MethodDeclaration methodDeclaration) {
        String commands = ".method public ";
        String arg = "";
        String locals = ".limit stack 128\n.limit locals 128\n";
        for(VarDeclaration var: methodDeclaration.getArgs())
            arg += makeTypeSignature(var.getType());
        if(methodDeclaration instanceof ConstructorDeclaration) {
            commands += "<init>(" + arg + ")V\n" + locals;
            commands += "aload_0\ninvokespecial ";
            if(this.currentClass.getParentClassName() == null)
                commands += "java/lang/Object/<init>()V\n";
            else
                commands += currentClass.getParentClassName().getName() + "/<init>()V\n";
            for(FieldDeclaration field: currentClass.getFields()){
                commands += "aload_0\n";
                Type t = field.getVarDeclaration().getType();
                commands += init(t);
                commands += "putfield " + currentClass.getClassName().getName() + "/" + field.getVarDeclaration().getVarName().getName() + " " + makeTypeSignature(t) + "\n";
            }
        }
        else
            commands += methodDeclaration.getMethodName().getName() + "(" + arg + ")" + makeTypeSignature(methodDeclaration.getReturnType()) + "\n" + locals;
        addCommand(commands);
        commands = "";
        for(VarDeclaration var: methodDeclaration.getLocalVars()){
            Integer slot = slotOf(var.getVarName().getName());
            commands += var.accept(this);
            commands += "astore " + slot.toString() + "\n";
        }
        addCommand(commands);
        commands = "";
        for(Statement stmt: methodDeclaration.getBody())
            stmt.accept(this);
        if(!currentMethod.getDoesReturn())
            commands += "return\n";
        commands += ".end method";
        addCommand(commands);
        return null;
    }

    @Override
    public String visit(FieldDeclaration fieldDeclaration) {
        return ".field " + fieldDeclaration.getVarDeclaration().getVarName().getName() + " " + makeTypeSignature(fieldDeclaration.getVarDeclaration().getType());
    }

    @Override
    public String visit(VarDeclaration varDeclaration) {
        return init(varDeclaration.getType());
    }

    @Override
    public String visit(AssignmentStmt assignmentStmt) {
        BinaryExpression assignExpr = new BinaryExpression(assignmentStmt.getlValue(), assignmentStmt.getrValue(), BinaryOperator.assign);
        addCommand(assignExpr.accept(this));
        addCommand("pop");
        return null;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        for (Statement stmt: blockStmt.getStatements())
            stmt.accept(this);
        return null;
    }

    @Override
    public String visit(ConditionalStmt conditionalStmt) {
        String commands = conditionalStmt.getCondition().accept(this);
        commands += "ifeq ";
        String elseLabel = generateLabel();
        commands += elseLabel + "\n";
        addCommand(commands);
        commands = "";
        if(conditionalStmt.getThenBody() != null)
            conditionalStmt.getThenBody().accept(this);
        String endifLabel = generateLabel();
        commands += "goto " + endifLabel + "\n";
        commands += elseLabel + ":\n";
        addCommand(commands);
        commands = "";
        if(conditionalStmt.getElseBody() != null)
            conditionalStmt.getElseBody().accept(this);
        commands += endifLabel + ":\n";
        addCommand(commands);
        return null;
    }

    @Override
    public String visit(MethodCallStmt methodCallStmt) {
        this.expressionTypeChecker.setIsInMethodCallStmt(true);
        addCommand(methodCallStmt.getMethodCall().accept(this));
        this.expressionTypeChecker.setIsInMethodCallStmt(false);
        addCommand("pop");
        return null;
    }

    @Override
    public String visit(PrintStmt print) {
        addCommand("getstatic java/lang/System/out Ljava/io/PrintStream;");
        addCommand(print.getArg().accept(this));
        Type t = print.getArg().accept(expressionTypeChecker);
        String arg;
        if(t instanceof IntType)
            arg = "I";
        else if(t instanceof BoolType)
            arg = "Z";
        else
            arg = "Ljava/lang/String;";
        addCommand("invokevirtual java/io/PrintStream/print(" + arg + ")V");
        return null;
    }

    @Override
    public String visit(ReturnStmt returnStmt) {
        Type type = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        if(type instanceof NullType)
            addCommand("return");
        else {
            addCommand(returnStmt.getReturnedExpr().accept(this));
            if(type instanceof IntType)
                addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;");
            else if(type instanceof BoolType)
                addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;");
            addCommand("areturn");
        }
        return null;
    }


    @Override
    public String visit(BreakStmt breakStmt) {
        addCommand("goto " + this.endLoopLabel.pop());
        return null;
    }

    @Override
    public String visit(ContinueStmt continueStmt) {
        addCommand("goto " + this.startLoopLabel.peek());
        return null;
    }

    @Override
    public String visit(ForeachStmt foreachStmt) {
        String cont = generateLabel();
        String brk = generateLabel();
        String rest = generateLabel();
        this.startLoopLabel.push(cont);
        this.endLoopLabel.push(brk);
        Integer slot = slotOf("");
        addCommand("ldc 0");
        addCommand("istore " + slot.toString());
        addCommand(rest+":");
        addCommand("iload " + slot.toString());
        addCommand(foreachStmt.getList().accept(this));
        addCommand("getfield List/elements Ljava/util/ArrayList;");
        addCommand("invokevirtual java/util/ArrayList/size()I");
        addCommand("if_icmpge "+ brk );
        addCommand(foreachStmt.getList().accept(this));
        addCommand("iload " + slot.toString());
        addCommand("invokevirtual List/getElement(I)Ljava/lang/Object;");
        Type t = ((ListType) foreachStmt.getList().accept(expressionTypeChecker)).getElementsTypes().get(0).getType();
        addCommand(checkCast(t));
        addCommand("astore " + slotOf(foreachStmt.getVariable().getName()));
        if(foreachStmt.getBody() !=  null)
            foreachStmt.getBody().accept(this);
        addCommand(cont+":");
        addCommand("iload " + slot.toString());
        addCommand("ldc 1");
        addCommand("iadd");
        addCommand("istore " + slot.toString());
        addCommand("goto " + rest);
        addCommand(brk+":");
        this.startLoopLabel.pop();
        return null;
    }

    @Override
    public String visit(ForStmt forStmt) {
        String cont = generateLabel();
        String brk = generateLabel();
        String rest = generateLabel();
        this.startLoopLabel.push(cont);
        this.endLoopLabel.push(brk);
        if(forStmt.getInitialize() != null)
            forStmt.getInitialize().accept(this);
        addCommand(rest+":");
        if(forStmt.getCondition() != null)
            addCommand(forStmt.getCondition().accept(this));
        else
            addCommand("ldc 1");
        addCommand("ldc 0");
        addCommand("if_icmpeq "+brk);
        if(forStmt.getBody() != null)
            forStmt.getBody().accept(this);
        addCommand(cont+":");
        if(forStmt.getUpdate() != null)
            forStmt.getUpdate().accept(this);
        addCommand("goto "+rest);
        addCommand(brk+":");
        this.startLoopLabel.pop();
        return null;
    }

    private String binaryAccept(BinaryExpression binaryExpression){
        String commands = "";
        commands += binaryExpression.getFirstOperand().accept(this);
        commands += binaryExpression.getSecondOperand().accept(this);
        return commands;
    }

    @Override
    public String visit(BinaryExpression binaryExpression) {
        String commands = "";
        BinaryOperator operator = binaryExpression.getBinaryOperator();
        if (operator == BinaryOperator.add) {
            commands += binaryAccept(binaryExpression);
            commands += "iadd\n";
        }
        else if (operator == BinaryOperator.sub) {
            commands += binaryAccept(binaryExpression);
            commands += "isub\n";
        }
        else if (operator == BinaryOperator.mult) {
            commands += binaryAccept(binaryExpression);
            commands += "imul\n";
        }
        else if (operator == BinaryOperator.div) {
            commands += binaryAccept(binaryExpression);
            commands += "idiv\n";
        }
        else if (operator == BinaryOperator.mod) {
            commands += binaryAccept(binaryExpression);
            commands += "irem\n";
        }
        else if((operator == BinaryOperator.gt) || (operator == BinaryOperator.lt)) {
            commands += binaryAccept(binaryExpression);
            String label1 = generateLabel();
            if(operator == BinaryOperator.gt)
                commands += "if_icmple ";
            else
                commands += "if_icmpge ";
            commands += label1 + "\n";
            commands += "ldc 1\n";
            String end = generateLabel();
            commands += "goto " + end + "\n" + label1 + ":\n";
            commands += "ldc 0 \n";
            commands += end + ":\n";
        }

        else if((operator == BinaryOperator.eq) || (operator == BinaryOperator.neq)) {
            commands += binaryAccept(binaryExpression);
            Type t = binaryExpression.getFirstOperand().accept(this.expressionTypeChecker);
            String Else = generateLabel();
            String After = generateLabel();
            if (t instanceof IntType || t instanceof BoolType) {
                if (operator == BinaryOperator.eq)
                    commands += "if_icmpeq " + Else + "\n";
                if (operator == BinaryOperator.neq)
                    commands += "if_icmpne " + Else + "\n";
            }
            else {
                if (operator == BinaryOperator.eq)
                    commands += "if_acmpeq " + Else + "\n";
                if (operator == BinaryOperator.neq)
                    commands += "if_acmpne " + Else + "\n";
            }
            commands += "ldc 0\n";
            commands += "goto " + After + "\n";
            commands += Else + ":" + "\n";
            commands += "ldc 1\n";
            commands += After + ":" + "\n";
        }
        else if(operator == BinaryOperator.and) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += "ifeq ";
            String label1 = generateLabel();
            commands += label1 + "\n";
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "ifeq " + label1 + "\n";
            String end = generateLabel();
            commands += "ldc 1\ngoto " + end + "\n";
            commands += label1 + ":\n";
            commands += "ldc 0\n";
            commands += end + ":\n";
        }
        else if(operator == BinaryOperator.or) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += "ifne ";
            String label1 = generateLabel();
            commands += label1 + "\n";
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "ifne " + label1 + "\n";
            String end = generateLabel();
            commands += "ldc 0\ngoto " + end + "\n";
            commands += label1 + ":\n";
            commands += "ldc 1\n";
            commands += end + ":\n";
        }
        else if(operator == BinaryOperator.assign) {
            Type firstType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
            Type secondType = binaryExpression.getSecondOperand().accept(expressionTypeChecker);
            String secondOperandCommands = binaryExpression.getSecondOperand().accept(this);
            if(firstType instanceof ListType)
                secondOperandCommands = "new List\ndup\n" + secondOperandCommands + "invokespecial List/<init>(LList;)V\n";
            if(binaryExpression.getFirstOperand() instanceof Identifier) {
                commands += secondOperandCommands;
                String id = ((Identifier) binaryExpression.getFirstOperand()).getName();
                if(secondType instanceof IntType)
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                if(secondType instanceof BoolType)
                    commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
                Integer slot = slotOf(id);
                commands += "astore " + slot.toString() + "\n";
                commands += binaryExpression.getFirstOperand().accept(this);
            }
            else if(binaryExpression.getFirstOperand() instanceof ListAccessByIndex) {
                ListAccessByIndex la = (ListAccessByIndex) binaryExpression.getFirstOperand();
                commands += la.getInstance().accept(this);
                commands += la.getIndex().accept(this);
                commands += secondOperandCommands;
                if(secondType instanceof IntType)
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                if(secondType instanceof BoolType)
                    commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                commands += binaryExpression.getFirstOperand().accept(this);
            }
            else if(binaryExpression.getFirstOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getInstance();
                Type memberType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    ObjectOrListMemberAccess firstOperand = (ObjectOrListMemberAccess) binaryExpression.getFirstOperand();
                    commands += firstOperand.getInstance().accept(this);
                    Integer idx = 0;
                    for(ListNameType l: ((ListType)instanceType).getElementsTypes()){
                        if(l.getName().getName().equals(memberName))
                            break;
                        idx++;
                    }
                    commands += "ldc " + idx.toString() + "\n";
                    commands += secondOperandCommands;
                    if(secondType instanceof IntType)
                        commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    if(secondType instanceof BoolType)
                        commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                    commands += binaryExpression.getFirstOperand().accept(this);
                }
                else if(instanceType instanceof ClassType) {
                    ObjectOrListMemberAccess firstOperand = (ObjectOrListMemberAccess) binaryExpression.getFirstOperand();
                    String className = ((ClassType) instanceType).getClassName().getName();
                    commands += firstOperand.getInstance().accept(this);
                    commands += secondOperandCommands;
                    if(secondType instanceof IntType)
                        commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    if(secondType instanceof BoolType)
                        commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
                    commands += "putfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += binaryExpression.getFirstOperand().accept(this);
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(UnaryExpression unaryExpression) {
        UnaryOperator operator = unaryExpression.getOperator();
        String commands = "";
        if(operator == UnaryOperator.minus) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ineg\n";
        }
        else if(operator == UnaryOperator.not) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ifne ";
            String label1 = generateLabel();
            commands += label1 + "\n";
            commands += "ldc 1\n";
            commands += "goto ";
            String end = generateLabel();
            commands += end + "\n";
            commands += label1 + ":\nldc 0\n" + end + ":\n";
        }
        else if((operator == UnaryOperator.predec) || (operator == UnaryOperator.preinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                Integer slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());
                commands += "aload " + slot.toString() + "\ninvokevirtual java/lang/Integer/intValue()I\n" + "ldc 1\n";
                if(operator == UnaryOperator.predec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";
                commands += "dup\ninvokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\nastore " + slot.toString()  + "\n";
            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                ListAccessByIndex la = (ListAccessByIndex)unaryExpression.getOperand();
                commands += la.getInstance().accept(this);
                commands += la.getIndex().accept(this);
                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "ldc 1\n";
                if(operator == UnaryOperator.predec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                Integer slot = slotOf("");
                commands += "astore " + slot.toString() + "\n";
                commands += la.getInstance().accept(this);
                commands += la.getIndex().accept(this);
                commands += "aload " + slot.toString() + "\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                commands += "aload " + slot.toString() + "\n" + "invokevirtual java/lang/Integer/intValue()I\n";
            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    Integer idx = 0;
                    for(ListNameType l: ((ListType)instanceType).getElementsTypes()){
                        if(l.getName().getName().equals(memberName))
                            break;
                        idx++;
                    }
                    commands += instance.accept(this);
                    commands += "ldc " + idx.toString() + "\n";
                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.predec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    Integer slot = slotOf("");
                    commands += "astore " + slot.toString() + "\n";
                    commands += instance.accept(this);
                    commands += "ldc " + idx.toString() + "\n";
                    commands += "aload " + slot.toString() + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                    commands += "aload " + slot.toString() + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                }
                else if(instanceType instanceof ClassType) {
                    String temp = instance.accept(this);
                    commands += temp;
                    temp += "getfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    temp += "invokevirtual java/lang/Integer/intValue()I\n";
                    temp += "ldc 1\n";
                    if(operator == UnaryOperator.predec)
                        temp += "isub\n";
                    else
                        temp += "iadd\n";
                    commands += temp;
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    commands += "putfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += instance.accept(this);
                    commands += "getfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                }
            }
        }
        else if((operator == UnaryOperator.postdec) || (operator == UnaryOperator.postinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                Integer slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());
                commands += "aload " + slot.toString() + "\ninvokevirtual java/lang/Integer/intValue()I\ndup\n" + "ldc 1\n";
                if(operator == UnaryOperator.postdec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\nastore " + slot.toString()  + "\n";
            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                ListAccessByIndex la = (ListAccessByIndex)unaryExpression.getOperand();
                commands += la.getInstance().accept(this);
                commands += la.getIndex().accept(this);
                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "ldc 1\n";
                if(operator == UnaryOperator.postdec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                Integer slot = slotOf("");
                commands += "astore " + slot.toString() + "\n";
                commands += la.getInstance().accept(this);
                commands += la.getIndex().accept(this);
                commands += "aload " + slot.toString() + "\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                commands += "aload " + slot.toString() + "\n" + "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "ldc 1\n";
                if(operator == UnaryOperator.postdec)
                    commands += "iadd\n";
                else
                    commands += "isub\n";
            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    Integer idx = 0;
                    for(ListNameType l: ((ListType)instanceType).getElementsTypes()){
                        if(l.getName().getName().equals(memberName))
                            break;
                        idx++;
                    }
                    commands += instance.accept(this);
                    commands += "ldc " + idx.toString() + "\n";
                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    Integer slot = slotOf("");
                    commands += "astore " + slot.toString() + "\n";
                    commands += instance.accept(this);
                    commands += "ldc " + idx.toString() + "\n";
                    commands += "aload " + slot.toString() + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                    commands += "aload " + slot.toString() + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";
                }
                else if(instanceType instanceof ClassType) {
                    String temp = instance.accept(this);
                    commands += temp;
                    temp += "getfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    temp += "invokevirtual java/lang/Integer/intValue()I\n";
                    temp += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        temp += "isub\n";
                    else
                        temp += "iadd\n";
                    commands += temp;
                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    commands += "putfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += instance.accept(this);
                    commands += "getfield " + ((ClassType)instanceType).getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(ObjectOrListMemberAccess objectOrListMemberAccess) {
        Type memberType = objectOrListMemberAccess.accept(expressionTypeChecker);
        Type instanceType = objectOrListMemberAccess.getInstance().accept(expressionTypeChecker);
        String memberName = objectOrListMemberAccess.getMemberName().getName();
        String commands = "";
        if(instanceType instanceof ClassType) {
            String className = ((ClassType) instanceType).getClassName().getName();
            try {
                SymbolTable classSymbolTable = ((ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + className, true)).getClassSymbolTable();
                try {
                    classSymbolTable.getItem(FieldSymbolTableItem.START_KEY + memberName, true);
                    commands += objectOrListMemberAccess.getInstance().accept(this);
                    commands += "getfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    if(memberType instanceof IntType)
                        commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    else if(memberType instanceof  BoolType)
                        commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                } catch (ItemNotFoundException memberIsMethod) {
                    commands += "new Fptr\ndup\n";
                    commands += objectOrListMemberAccess.getInstance().accept(this);
                    commands += "ldc \"" + memberName + "\"\n";
                    commands += "invokespecial Fptr/<init>(Ljava/lang/Object;Ljava/lang/String;)V\n";
                }
            } catch (ItemNotFoundException classNotFound) { }
        }
        else if(instanceType instanceof ListType) {
            Integer idx = 0;
            for(ListNameType l: ((ListType)instanceType).getElementsTypes()){
                if(l.getName().getName().equals(memberName))
                    break;
                idx++;
            }
            commands += objectOrListMemberAccess.getInstance().accept(this);
            commands += "ldc " + idx.toString() + "\n";
            commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
            commands += checkCast(memberType);
            if(memberType instanceof IntType)
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
            else if(memberType instanceof  BoolType)
                commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        }
        return commands;
    }

    @Override
    public String visit(Identifier identifier) {
        String commands = "";
        Type t = identifier.accept(this.expressionTypeChecker);
        int slot = slotOf(identifier.getName());
        commands += "aload " + slot + "\n";
        if(t instanceof BoolType)
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        else if(t instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        return commands;
    }

    @Override
    public String visit(ListAccessByIndex listAccessByIndex) {
        String commands = "";
        Type memberType = listAccessByIndex.accept(this.expressionTypeChecker);
        commands += listAccessByIndex.getInstance().accept(this);
        commands += listAccessByIndex.getIndex().accept(this);
        commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
        commands += checkCast(memberType);
        if(memberType instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        else if(memberType instanceof  BoolType)
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        return commands;
    }

    @Override
    public String visit(MethodCall methodCall) {
        String commands = "";
        commands += methodCall.getInstance().accept(this);
        commands += "new java/util/ArrayList\ndup\ninvokespecial java/util/ArrayList/<init>()V\n";
        for(Expression e : methodCall.getArgs()) {
            commands += "dup\n";
            commands += e.accept(this);
            Type t = e.accept(this.expressionTypeChecker);
            if(t instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
            if(t instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\npop\n";
        }
        commands += "invokevirtual Fptr/invoke(Ljava/util/ArrayList;)Ljava/lang/Object;\n";
        Type t = methodCall.accept(expressionTypeChecker);
        commands += checkCast(t);
        if(t instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        else if(t instanceof  BoolType)
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        return commands;
    }

    @Override
    public String visit(NewClassInstance newClassInstance) {
        String commands = "";
        String arg = "";
        commands += "new " + newClassInstance.getClassType().getClassName().getName() + "\n";
        commands += "dup\n";
        for(Expression e : newClassInstance.getArgs()) {
            commands += e.accept(this);
            Type t = e.accept(this.expressionTypeChecker);
            if(t instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
            if(t instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            arg += makeTypeSignature(t);
        }
        commands += "invokespecial " + newClassInstance.getClassType().getClassName().getName() + "/<init>(" + arg + ")V\n";
        return commands;
    }

    @Override
    public String visit(ThisClass thisClass) {
        String commands = "";
        commands += "aload_0\n";
        return commands;
    }

    @Override
    public String visit(ListValue listValue) {
        String commands = "";
        commands += "new List\ndup\nnew java/util/ArrayList\ndup\ninvokespecial java/util/ArrayList/<init>()V\n";
        for(Expression e : listValue.getElements()) {
            commands += "dup\n";
            commands += e.accept(this);
            Type t = e.accept(this.expressionTypeChecker);
            if(t instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
            else if(t instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            commands += "checkcast java/lang/Object\ninvokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\npop\n";
        }
        commands += "invokespecial List/<init>(Ljava/util/ArrayList;)V\n";
        return commands;
    }

    @Override
    public String visit(NullValue nullValue) {
        String commands = "";
        commands += "aconst_null\n";
        return commands;
    }

    @Override
    public String visit(IntValue intValue) {
        String commands = "";
        commands += "ldc " + intValue.getConstant() + "\n";
        return commands;
    }

    @Override
    public String visit(BoolValue boolValue) {
        String commands = "";
        if(boolValue.getConstant())
            commands += "ldc 1\n";
        else
            commands += "ldc 0\n";
        return commands;
    }

    @Override
    public String visit(StringValue stringValue) {
        String commands = "";
        commands += "ldc \"" + stringValue.getConstant() + "\"\n";
        return commands;
    }

}
