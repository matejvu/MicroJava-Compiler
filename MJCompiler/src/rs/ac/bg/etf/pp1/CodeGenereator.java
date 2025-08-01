package rs.ac.bg.etf.pp1;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.concurrent.ConcurrentLinkedQueue;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class CodeGenereator extends VisitorAdaptor {

	int mainPc = 0;
	int dataSize = 0;
	private Stack<Integer> skipCondFact = new Stack<Integer>();
	private Stack<Integer> skipCondition = new Stack<Integer>();
	private Stack<Integer> skipThen = new Stack<Integer>();
	private Stack<Integer> skipElse = new Stack<Integer>();
	private Stack<Integer> doIdentAddr = new Stack<Integer>();
	private Stack<List<Integer>> breakAddr = new Stack<>();
	private Stack<List<Integer>> continueAddr = new Stack<>();
	private boolean globalEnded = false;
	private int globalVarCounter = 0;
	private Queue<Obj> classes = new ConcurrentLinkedQueue<>();
	private HashMap<Struct, Integer> TVF_ADDR = new HashMap<>();
	int TVF_init_addr = 0;
	private boolean shiftDesign;
	Obj cur_meth = Tab.noObj;
	private boolean programStarted;
	
	
	public int getMainPc() {
		return this.mainPc;
	}
	
	public int getDataSize() {
		return this.dataSize;
	}
	
	
	//==========INITIALIZATION==========
	
	
	public void init() {
		// 'ord' and 'chr' are the same code.
		Obj ordMethod = Tab.find("ord");
		Obj chrMethod = Tab.find("chr");
		ordMethod.setAdr(Code.pc);
		chrMethod.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.exit);
		Code.put(Code.return_);

		Obj lenMethod = Tab.find("len");
		lenMethod.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		Code.put(Code.exit);
		Code.put(Code.return_);
		
		Stack<Integer> skipToEnd = new Stack<>();
		Stack<Integer> skipToEndNoTrash = new Stack<>();
		Obj addMethod = Tab.find("add");
		addMethod.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(2); //argumenti
		Code.put(3); //arg + lokalne(br koriscenih)
		//provera popunjenosti
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		Code.loadConst(1);
		Code.put(Code.sub);//duzina niza na steku
		Code.put(Code.load_n);
		Code.loadConst(0);
		Code.put(Code.aload);//broj zauzetih na steku
		Code.put(Code.dup);
		Code.put(Code.store_2);//sacuvati u lok prom.
		Code.putFalseJump(Code.gt, 0);
		skipToEndNoTrash.push(Code.pc - 2);
		//da li je vec u setu
		Code.put(Code.load_n); //argument a
		Code.loadConst(0);
		//petlja
		int loopStart = Code.pc;
		Code.loadConst(1);
		Code.put(Code.add);
		//uslov petlje
		Code.put(Code.dup); //i
		Code.put(Code.load_2);//br el
		Code.putFalseJump(Code.le, 0);
		int skipToAdding = (Code.pc - 2);
		//telo petlje
		Code.put(Code.dup2);//da bi ostalo a i na steku 
		Code.put(Code.aload);//dohvatanje a[++i] ,zbog prvog sakrvienog el.
		Code.put(Code.load_1); //argument b
		Code.putFalseJump(Code.ne, 0); //ako su eq idi na kraj
		skipToEnd.push(Code.pc - 2);
		Code.putJump(loopStart);
		//nakon petlje
		Code.fixup(skipToAdding);
		//a i na steku, updejtuj niz
		Code.put(Code.dup2);//da bi imalo sta da se skida i u ovom slucaju
		Code.put(Code.dup2); //dupliraj a i
		Code.put(Code.load_1); //ucitaj b
		Code.put(Code.astore); //a[i] = b
		Code.loadConst(0); //a i 0
		Code.put(Code.dup_x1); //a 0 i 0
		Code.put(Code.pop);
		Code.put(Code.astore); //a[0] = i; updejtovan br el		
		//ciscenje i izalaz
		while(!skipToEnd.isEmpty())
			Code.fixup(skipToEnd.pop());
		Code.put(Code.pop);
		Code.put(Code.pop);//skidanje djubreta
		while(!skipToEndNoTrash.isEmpty())
			Code.fixup(skipToEndNoTrash.pop());
		Code.put(Code.exit);
		Code.put(Code.return_);
		
		Stack<Integer> exitLoop = new Stack<Integer>();
		Obj addAllMethod = Tab.find("addAll");
		addAllMethod.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(2);
		Code.put(2);//a, b
		//pocetak
		Code.put(Code.load_1);	//..., b
		Code.loadConst(0);		//..., b, 0
		//uslov petlje
		int loopAdr = Code.pc;
		Code.put(Code.dup);		//..., b, 0, 0
		Code.put(Code.load_1);	//..., b, 0, 0, b
		Code.put(Code.arraylength); //..., b, 0, 0, len(b)
		Code.putFalseJump(Code.lt, 0); //izlazi sa stanjem: b,0
		exitLoop.push(Code.pc - 2); //..., b, 0
		//telo petlje
		Code.put(Code.dup2);	//..., b, 0, b, 0
		Code.put(Code.aload);	//..., b, 0, b[i]
		
		Code.put(Code.load_n);	//..., b, 0, b[i], a
		Code.put(Code.dup_x1);	//..., b, 0, a, b[i], a
		Code.put(Code.pop);		//..., b, 0, a, b[i]
		int offset = addMethod.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset); //..., b, 0
		Code.loadConst(1);
		Code.put(Code.add); 			//..., b, 1
		Code.putJump(loopAdr);
		
		while(!exitLoop.isEmpty())
			Code.fixup(exitLoop.pop());
		Code.put(Code.pop);
		Code.put(Code.pop);
		Code.put(Code.exit);
		Code.put(Code.return_);		
	}
	
	
	//==========METHODS==========
	
	
	@Override
	public void visit(MethodChoice_Type methodChoice) {
		methodChoice.obj.setAdr(Code.pc);
//		if(methodChoice.getI2().equalsIgnoreCase("main"))
//			this.mainPc = Code.pc;
		
		Code.put(Code.enter);
		Code.put(methodChoice.obj.getLevel()); //b1
		Code.put(methodChoice.obj.getLocalSymbols().size()); //b2
		
		for(Obj el: methodChoice.obj.getLocalSymbols()) {
			if(el.getName().equalsIgnoreCase("this")) {
				int numActPars = methodChoice.obj.getLevel();
				System.out.println(numActPars + "=-=-");
				Code.put(Code.store); //dohvati this iz polimorfnog poziva 
				Code.put(numActPars); //jer je this prvi lok parametar, ne formalni
				break;
			}
		}
		
		cur_meth = methodChoice.obj;
	}
	
	@Override
	public void visit(MethodChoice_Void methodChoice) {
		methodChoice.obj.setAdr(Code.pc);
		if(methodChoice.getI1().equalsIgnoreCase("main"))
			this.mainPc = Code.pc;
		
		Code.put(Code.enter);
		Code.put(methodChoice.obj.getLevel()); //b1
		Code.put(methodChoice.obj.getLocalSymbols().size()); //b2
		
		if(methodChoice.getI1().equalsIgnoreCase("main")) {
//			inicijalizacija TVF na pocetku main-a
			int offset = TVF_init_addr - Code.pc;
			Code.put(Code.call);
			Code.put2(offset); //poziv init TVF
		}
		
		for(Obj el: methodChoice.obj.getLocalSymbols()) {
			if(el.getName().equalsIgnoreCase("this")) {
				int numActPars = methodChoice.obj.getLevel();
				System.out.println(numActPars + "=-=-");
				Code.put(Code.store); //dohvati this iz polimorfnog poziva 
				Code.put(numActPars); //jer je this prvi lok parametar, ne formalni
				break;
			}
		}
		
		cur_meth = methodChoice.obj;
	}
	
	@Override
	public void visit(MethodDecl methodDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	
	//==========PRINT==========
	
	
	@Override
	public void visit(Statement_Print printStatement) {
		
		if(printStatement.getExpr().struct.equals(Tab.charType))
			Code.put(Code.bprint);
		else if(printStatement.getExpr().struct.equals(ExtendedTab.setType)) {
			this.setPrint(printStatement);
		}
		else
			Code.put(Code.print);
	}
	
	private void setPrint(Statement_Print printStatement) {
		Stack<Integer> skipLoop = new Stack<Integer>();
		//..., adr, with	
		Code.put(Code.dup_x1);
		Code.put(Code.pop); 	//..., with, adr
		Code.loadConst(0); 		//..., with, adr, 0
		Code.put(Code.dup2);	//..., with, adr, 0, adr, 0
		Code.put(Code.aload); 	//..., with, adr, 0, set[0]
		
		int loopBegining = Code.pc;
		Code.put(Code.dup2);	//..., with, adr, i, set[0], i, set[0]
		Code.putFalseJump(Code.lt, 0);//iskoci ako su jednaki(..., with, adr, i, set[0])
		skipLoop.push(Code.pc - 2);
		
		Code.put(Code.dup_x2);	//..., with, set[0], adr, 0, set[0]
		Code.put(Code.pop);		//..., with, set[0], adr, 0
		
		Code.put(Code.dup_x1);	//..., with, set[0], 0, adr, 0
		Code.put(Code.pop);		//..., with, set[0], 0, adr
		Code.put(Code.dup_x2);	//..., with, adr, set[0], 0, adr
		Code.put(Code.dup_x1);	//..., with, adr, set[0], adr, 0, adr
		Code.put(Code.pop);		//..., with, adr, set[0], adr, 0
		
		Code.loadConst(1);
		Code.put(Code.add);		//..., with, adr, set[0], adr, i
		Code.put(Code.dup_x1);	//..., with, adr, set[0], i, adr, i
		Code.put(Code.aload);	//..., with, adr, set[0], i, set[i]
		Code.loadConst(0);		//..., with, adr, set[0], i, set[i], 0
		Code.put(Code.print);
		Code.loadConst(' ');	//..., with, adr, set[0], i, '\b'
		Code.loadConst(0);		//..., with, adr, set[0], i, '\b', 0
		Code.put(Code.bprint);
		Code.put(Code.dup_x1);	//..., with, adr, i, set[0], i,
		Code.put(Code.pop);		//..., with, adr, i, set[0],	
		Code.putJump(loopBegining);
		
		while(!skipLoop.isEmpty())
			Code.fixup(skipLoop.pop());
		//..., with, adr, i, set[0]
		Code.put(Code.pop);
		Code.put(Code.pop);
		Code.put(Code.pop);
		Code.put(Code.pop);
		Code.loadConst('\n');
		Code.loadConst(0);
		Code.put(Code.bprint);
	}


	@Override
	public void visit(StatementNumOpt_ printStatement) {
		Code.loadConst(printStatement.getN1());
	}
	
	@Override
	public void visit(StatementNumOpt_Epsilon printStatement) {
		Code.loadConst(0);
	}
	
	
	//==========FACTOR==========
	
	
	@Override
	public void visit(Factor_Number factor) {
		Code.loadConst(factor.getN1());
	}
	
	@Override
	public void visit(Factor_Character factor) {
		Code.loadConst(factor.getC1());
	}
	
	@Override
	public void visit(Factor_Bool factor) {
		Code.loadConst(factor.getB1());
	}
	
	@Override
	public void visit(Factor_Designator factor) {
		if(factor.getFactorDesignatorOpt() instanceof FactorDesignatorOpt_)return;
		Code.load(factor.obj); //bolje da bi sse uracunao ii povratni tip ako se desi da je poziv memtode ipak
	}
	
	@Override
	public void visit(FactorOpt_Minus factor) {
		Code.put(Code.neg);
	}
	
	@Override
	public void visit(Factor_New factor) {
		if(factor.getFactorNewChoice() instanceof FactorNewChoice_Expr) {
			if(factor.getType().struct.equals(ExtendedTab.setType)) {
				//Set
				Code.loadConst(1);
				Code.put(Code.add);//Poveca se broj el. niza za 1
				Code.put(Code.newarray);
				Code.put(1);
				//Strutura skupa:
				//[0] - trenutno el u skupu
				//[1..N] - elementi skupa
			}
			else {
				//Array
				Code.put(Code.newarray);
				if(factor.getType().struct.equals(Tab.charType))
					Code.put(0);
				else
					Code.put(1);
			}
		}
		else if(factor.getFactorNewChoice() instanceof FactorNewChoice_ActPars) {
			Code.put(Code.new_);
			int numVars = factor.getType().struct.getNumberOfFields();
			Code.put2(4*numVars);  //((int)numVars); u numVar se broji i _tvf_
			
			//tvf_pt
			Code.put(Code.dup);		//duplira se adr
			Code.loadConst(TVF_ADDR.get(factor.getType().struct)); //stvlja se vrednost polja
			Code.put(Code.putfield);
			Code.put2(0); 	//_tvf_ je nulto polje
			
		}
	}
	
	//==========EXPR==========
	
	
	@Override
	public void visit(ExprTermList_ exprTerm) {
		if(exprTerm.getAddop() instanceof Addop_Plus)
			Code.put(Code.add);
		else if(exprTerm.getAddop() instanceof Addop_Minus)
			Code.put(Code.sub);
	}
	
	
	//==========TERM==========
	
	
	@Override
	public void visit(TermFactorList_ termFactor) {
		if(termFactor.getMulop() instanceof Mulop_Mult)
			Code.put(Code.mul);
		else if(termFactor.getMulop() instanceof Mulop_Div)
			Code.put(Code.div);
		else if(termFactor.getMulop() instanceof Mulop_Mod)
			Code.put(Code.rem);
	}
	
	
	//==========DESIGNATOR==========
	
	@Override
	public void visit(DesignatorList_Epsilon designator) {
		
		if(designator.obj.getKind() == Obj.Fld 
			|| (designator.obj.getKind() == Obj.Meth && globalEnded && !programStarted)) {
			int numFormPars = cur_meth.getLevel();
			Code.put(Code.load);
			Code.put(numFormPars); //ucitaj this
			if(designator.obj.getKind() == Obj.Meth)shiftDesign = true;
//			System.out.println("Ucitava se polje "+designator.obj.getName());
			//if()
		}
		if(designator.getParent() instanceof DesignatorList_Expr
		|| designator.getParent() instanceof DesignatorList_Ident)
			Code.load(designator.obj);
	}
	
	@Override
	public void visit(DesignatorList_Expr designator) {
		if(designator.getParent() instanceof DesignatorList_Expr)
			Code.load(designator.obj);
		if(designator.getParent() instanceof DesignatorList_Ident) {
			DesignatorList_Ident dli = (DesignatorList_Ident)designator.getParent();
			Code.load(designator.obj);
//			if(dli.obj.getKind() == Obj.Meth) {
//				System.out.println("Usao uuu "+designator.obj.getName());
//				Code.put(Code.dup2);
//				
//			}
		}
	}
	
	@Override
	public void visit(DesignatorList_Ident designator) {
		if(designator.obj.getKind() == Obj.Meth)shiftDesign = true;
		
		if(designator.getParent() instanceof DesignatorList_Expr
		|| designator.getParent() instanceof DesignatorList_Ident) {
			if(designator.obj.getKind() == Obj.Meth) {
				System.out.println("DDD: "+designator.getDesignator().obj.getName() + ExtendedTab.ObjToString(designator.getDesignator().obj));
//				if(designator.getDesignator().obj.getKind() != Obj.Elem)
					Code.load(designator.getDesignator().obj);  //za this  ???????
			}
			else {
				Code.load(designator.obj);
				System.out.println("Polje: "+designator.obj.getName());
			}
		}
	}
	
//	@Override
//	public void visit(DesignatorLBrack LBrack) {
//		SyntaxNode parent = LBrack.getParent();
//		if (parent instanceof DesignatorList_Expr) {
//		    DesignatorList_Expr node = (DesignatorList_Expr) parent;
//		    Code.load(node.getDesignator().obj);
//		}
//		else System.err.println("Nesto nije ok sa [");
//	}
	
	
	//==========ACT PARS==========
	
	
	@Override
	public void visit(ActParsOpt_Epsilon actPars) {
		if(shiftDesign)Code.put(Code.dup);
	}
	@Override
	public void visit(ActPars_Epsilon actPars) {
		if(shiftDesign) {
			Code.put(Code.dup_x1); 	//expr, des, expr
			Code.put(Code.pop);		//expr, des
			Code.put(Code.dup_x1);	//des, expr, des
		}
	}
	@Override
	public void visit(ActPars_ actPars) {
		if(shiftDesign) {
									// ..., des, expr
			Code.put(Code.dup_x1); 	//expr, des, expr
			Code.put(Code.pop);		//expr, des
		}
	}
	
	
	//==========DESIGNATOR DECLARATIONS==========
	
	
	@Override
	public void visit(DesignatorChoice_Assignop assign) {
		SyntaxNode parent = assign.getParent();
		if (parent instanceof Designator_Choice) {
			Designator_Choice node = (Designator_Choice) parent;
			Obj leftSideObj = node.getLeftSideDesignatorStatement().getDesignator().obj;
		    
			if(leftSideObj.getKind() == Obj.Fld) {
				
			}
			
			Code.store(leftSideObj);
		}
		else System.err.println("Nesto nije ok sa dodelom(=)");
	}
	
	@Override
	public void visit(DesignatorChoice_Inc designatoChoice) {
		SyntaxNode parent = designatoChoice.getParent();
		if (parent instanceof Designator_Choice) {
			Designator_Choice node = (Designator_Choice) parent;
			Obj leftSideObj = node.getLeftSideDesignatorStatement().getDesignator().obj;
		    
			if(leftSideObj.getKind() == Obj.Elem) 
				Code.put(Code.dup2);
			else if(leftSideObj.getKind() == Obj.Fld)
				Code.put(Code.dup);
			
			Code.load(leftSideObj);
			Code.loadConst(1);
			Code.put(Code.add);
			Code.store(leftSideObj);
		}
		else System.err.println("Nesto nije ok sa inkrementiranjem(++)");
	}
	
	@Override
	public void visit(DesignatorChoice_Dec designatoChoice) {
		SyntaxNode parent = designatoChoice.getParent();
		if (parent instanceof Designator_Choice) {
			Designator_Choice node = (Designator_Choice) parent;
			Obj leftSideObj = node.getLeftSideDesignatorStatement().getDesignator().obj;
		    
			if(leftSideObj.getKind() == Obj.Elem) 
				Code.put(Code.dup2);
			else if(leftSideObj.getKind() == Obj.Fld)
				Code.put(Code.dup);
			
			Code.load(leftSideObj);
			Code.loadConst(1);
			Code.put(Code.sub);
			Code.store(leftSideObj);
		}
		else System.err.println("Nesto nije ok sa dekrementiranjem(--)");
	}
	
	
	//==========STATEMENTS==========

	
	@Override
	public void visit(Statement_Return statement) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(Statement_Read statement) {
		
		if(statement.getDesignator().obj.getType().equals(Tab.charType))
			Code.put(Code.bread);
		else
			Code.put(Code.read);
	
		Code.store(statement.getDesignator().obj);
		
	}
	
	//==================================
	
	private boolean isVirtual(Designator_Choice dc, Obj ret) {
		SyntaxNode designatorNode = dc.getLeftSideDesignatorStatement().getDesignator();
		String methName= ret.getName();
		if(designatorNode instanceof DesignatorList_Ident) {
			DesignatorList_Ident dli = (DesignatorList_Ident)designatorNode;
			ret = dli.getDesignator().obj;
			
//			System.out.print("Designator: " + ret.getName());
//			System.out.println("  |yes virt");
			polymorphCall(ret, methName);
			return true;
		}
		
//		System.out.print("Designator: " + ret.getName());
//		System.out.println("  |no virt");
		return false;
	}
	
	private int polymorphCall(Obj designator, String methName) {
//		Code.put(Code.pop); //zato sto se ne koristi adr metode za invoke virtual

		shiftDesign = false;
//		Code.load(designator);				//obj

		Code.put(Code.getfield);
		Code.put2(0);						//_tvf_
		
		
		Code.put(Code.invokevirtual);
		for(char c: methName.toCharArray())
			Code.put4(c);
		Code.put4(-1);
		
//		Code.put(Code.pop);  //potenicjalno zbog designatora ispod
		
		return 0;
	}
	
	
	//==========INVOKE METHODS==========
	
	
	@Override
	public void visit(Designator_Choice designator) {
		
		if(! (designator.getDesignatorChoice() instanceof DesignatorChoice_ActPars)) return;
		
		Obj designator_obj = designator.getLeftSideDesignatorStatement().getDesignator().obj;
		int offset = designator_obj.getAdr() - Code.pc;
		
		if(!isVirtual(designator, designator_obj)) {
			Code.put(Code.call);
			Code.put2(offset);
		}
		
		System.out.println(designator_obj.getName());
		if(designator_obj.getType() != Tab.noType) {
			Code.put(Code.pop);
		}
	}
	
	@Override
	public void visit(FactorDesignatorOpt_ designator) {
		SyntaxNode parent = designator.getParent();
		if(parent instanceof Factor_Designator) {
			Factor_Designator fd = (Factor_Designator) parent;
			Obj designator_obj = fd.getDesignator().obj;
			
			if(fd.getDesignator() instanceof DesignatorList_Ident) {
				String methName = designator_obj.getName();
				DesignatorList_Ident dli = (DesignatorList_Ident)fd.getDesignator();
				designator_obj = dli.getDesignator().obj;
//				System.out.println("EXPR Designator: " + designator_obj.getName()+"  |virt");
				polymorphCall(designator_obj, methName);
			}
			else if(fd.getDesignator() instanceof DesignatorList_Epsilon && globalEnded && !programStarted) {
				String methName = designator_obj.getName();
				polymorphCall(designator_obj, methName);
			}
			else {
//				System.out.println("EXPR Designator: " + designator_obj.getName()+"  |no virt");
				int offset = designator_obj.getAdr() - Code.pc;
				Code.put(Code.call);
				Code.put2(offset);
			}
			
		}
	}
	
	
	//==========CONDITIONS==========
	
	
	// Condition
	private int returnRelop(Relop relop) {
	    if (relop instanceof Relop_Eq)
	        return Code.eq;
	    else if (relop instanceof Relop_Ne)
	        return Code.ne;
	    else if (relop instanceof Relop_Lt)
	        return Code.lt;
	    else if (relop instanceof Relop_Le)
	        return Code.le;
	    else if (relop instanceof Relop_Gt)
	        return Code.gt;
	    else if (relop instanceof Relop_GE)
	        return Code.ge;
	    return 0;
	}

	@Override
	public void visit(CondFact condFact) {
		if(condFact.getCondFactExprOpt() instanceof CondFactExprOpt_Epsilon) {
			Code.loadConst(0);
			Code.putFalseJump(Code.ne, 0); //false
			skipCondFact.push(Code.pc - 2);
			//true
		}
		else if(condFact.getCondFactExprOpt() instanceof CondFactExprOpt_) {
			CondFactExprOpt_ cfeo = (CondFactExprOpt_)condFact.getCondFactExprOpt();
			Code.putFalseJump(this.returnRelop(cfeo.getRelop()), 0); //false
			skipCondFact.push(Code.pc - 2);
			//true;
		}
	}
	
	@Override
	public void visit(CondTerm condTerm) {
		Code.putJump(0); //then
		skipCondition.push(Code.pc - 2);
		
		//false
		while(!skipCondFact.isEmpty())
			Code.fixup(skipCondFact.pop());
	}
	
	@Override
	public void visit(Condition_ cond) {
		Code.putJump(0); //else
		skipThen.push(Code.pc - 2);
		
		//true
		while(!skipCondition.isEmpty())
			Code.fixup(skipCondition.pop());
	}
	
	
	//==========IF STATEMENT==========
	
	
	@Override
	public void visit(ElseIdent else_) {
		Code.putJump(0); //end
		skipElse.push(Code.pc - 2);
		
		//false
		Code.fixup(skipThen.pop());
	}
	
	@Override
	public void visit(Statement_If statementIf) {
		if(statementIf.getStatementElseOpt() instanceof StatementElseOpt_Epsilon)
			//no else statement
			Code.fixup(skipThen.pop());
		else if(statementIf.getStatementElseOpt() instanceof StatementElseOpt_)
			//yes else statement
			Code.fixup(skipElse.pop());
	}
	
	
	//==========DO WHILE STATEMENT==========
	
	
	@Override
	public void visit(DoWhileBegin doWhileBegin) {
		doIdentAddr.push(Code.pc);
		breakAddr.push(new ArrayList<Integer>());
		continueAddr.push(new ArrayList<Integer>());
	}
	
	@Override
	public void visit(Statement_Do statementDo) {
		//true
		Code.putJump(doIdentAddr.pop());
		//false
		Code.fixup(skipThen.pop());
		
		//za break
		while(!breakAddr.peek().isEmpty())
			Code.fixup(breakAddr.peek().remove(0));
		breakAddr.pop();
	}
	
	
	//==========BREAK AND CONITNUE==========
	
	
	@Override
	public void visit(Statement_Break statement) {
		Code.putJump(0);
		breakAddr.peek().add(Code.pc - 2);
	}
	
	@Override
	public void visit(Statement_Continue statement) {
		Code.putJump(0);
		continueAddr.peek().add(Code.pc - 2);
	}

	@Override
	public void visit(WhileNonTerm while_) {
		while(!continueAddr.peek().isEmpty())
			Code.fixup(continueAddr.peek().remove(0));
		continueAddr.pop();
	}
	
	//==========SETOP==========
	
	
	@Override
	public void visit(Designator_Designator unionStatement) {
		//dst = src1 union src2
		Obj dst = unionStatement.getLeftSideDesignatorStatement().getDesignator().obj;
		Obj src1 = unionStatement.getFirstSet().getDesignator().obj;
		Obj src2 = unionStatement.getDesignator().obj;
		Obj addAllMeth = Tab.find("addAll");
		
		
		Code.load(dst); 			//dst
		Code.load(src1);			//dst, src1
		Code.loadConst(1);
		Code.put(Code.add);			//dst, src1+1
		int offset = addAllMeth.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset); 
		
		Code.load(dst); 			//dst
		Code.load(src2);			//dst, src2
		Code.loadConst(1);
		Code.put(Code.add);			//dst, src2+1
		offset = addAllMeth.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset);
		
	
	}
	
	
	//==========MAP==========
	
	@Override
	public void visit(Expr_Map exprMap) {
		Stack<Integer> exitLoop = new Stack<>();
		Obj func = exprMap.getDesignator().obj;
		Obj arr = exprMap.getDesignator1().obj;
		
		//inicijalizacija
		Code.loadConst(0);
		Code.load(arr); 				// 0, arr
		Code.loadConst(0);				// 0, arr, 0
		
		int loopBegining = Code.pc;
		//uslov petlje
		Code.put(Code.dup);				// sum, arr, 0, 0
		Code.load(arr);					// sum, arr, 0, 0, arr
		Code.put(Code.arraylength);		// sum, arr, 0, 0, len(arr)
		Code.putFalseJump(Code.lt, 0);	// sum, arr, 0
		exitLoop.push(Code.pc - 2);
		//telo petlje
		Code.put(Code.dup2);			// sum, arr, i, arr, i
		Code.put(Code.aload);			// sum, arr, i, arr[i]
		int offset = func.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset); 				// sum, arr, i, func(arr[i)
		Code.put(Code.dup_x2);			// sum, func(arr[i]), arr, i, func(arr[i)
		Code.put(Code.pop);				// sum, func(arr[i]), arr, i
		Code.put(Code.dup_x1);			// sum, func(arr[i]), i, arr, i
		Code.put(Code.pop);				// sum, func(arr[i]), i, arr
		Code.put(Code.pop);				// sum, func(arr[i]), i
		Code.put(Code.dup_x2);			// i, sum, func(arr[i]), i
		Code.put(Code.pop);				// i, sum, func(arr[i])
		Code.put(Code.add);				// i, new_sum
		Code.put(Code.dup_x1);			// new_sum, i, new_sum
		Code.put(Code.pop);				// new_sum, i
		Code.loadConst(1);				// new_sum, i, 1
		Code.put(Code.add);				// new_sum, i+1
		Code.load(arr);					// new_sum, i+1, arr
		Code.put(Code.dup_x1);			// new_sum, arr, i+1, arr
		Code.put(Code.pop);				// new_sum, arr, i+1
		Code.putJump(loopBegining);
	
		while(!exitLoop.isEmpty())
			Code.fixup(exitLoop.pop());
		
		Code.put(Code.pop);
		Code.put(Code.pop);
		// ..., sum
	}
	
	
	//==========COUNT GLOBAL VARS==========
	
	@Override
	public void visit(MethodDeclList_Epsilon ident) {
		globalEnded = true; //zavrsio sa globalnim domenom
		programStarted = true;
		initTVF();
	}
	@Override
	public void visit(ClassHeader ident) {
		globalEnded = true;//usao u klasu
		classes.add(ident.obj);
	}
	@Override
	public void visit(ClassDecl ident) {
		globalEnded = false; //izasao iz klase
	}
	@Override
	public void visit(VarList_Ident ident) {
		if(!globalEnded)
			globalVarCounter ++;
	}
	@Override
	public void visit(VarList_Type ident) {
		if(!globalEnded)
			globalVarCounter ++;
	}
	
	
	//==========TVF==========
	
	private void initTVF() {
		
		System.out.println("============TVF============");
		
		TVF_init_addr = Code.pc;
		Code.put(Code.enter);
		Code.put(0);
		Code.put(0);
		
		int sc = globalVarCounter;
		for(Obj classObj: classes) {

			Struct classStruct = classObj.getType();
			System.out.println("Klasa "+classObj.getName()+" ["+sc+"]");

			TVF_ADDR.put(classStruct, sc);
			
			//incijalizacija ulaza
			for(Obj cur: classStruct.getMembers()) {
				if(cur.getKind() != Obj.Meth)continue;
					
				for(char c: cur.getName().toCharArray()) {
					Code.loadConst(c);
					Code.put(Code.putstatic);
					Code.put2(sc++);
					
				}
				Code.loadConst(-1);
				Code.put(Code.putstatic);
				Code.put2(sc++);
				
				if(cur.getAdr() == -1) {
					//naslediti od roditelja
					Struct parent = classStruct.getElemType();
					if(parent != null && !parent.equals(Tab.noType)) {
						for(Obj cur_impl: parent.getMembers()) {
							if(cur_impl.getKind() != Obj.Meth) continue;
							if(cur_impl.getName().equals(cur.getName())) {
								cur.setAdr( cur_impl.getAdr());
								break;
							}
						}
					}
					if(classStruct.getImplementedInterfaces() != null
							&& classStruct.getImplementedInterfaces().iterator().hasNext()) {
						
						Struct interfaceS = classStruct.getImplementedInterfaces().iterator().next();
						for(Obj cur_impl: interfaceS.getMembers()) {
							if(cur_impl.getKind() != Obj.Meth) continue;
							if(cur_impl.getName().equals(cur.getName())) {
								cur.setAdr( cur_impl.getAdr());
								break;
							}
						}
					}
					
					if(cur.getAdr() == -1)System.err.println("Greska pri nasledjivanju adr metode");
				}
				
				System.out.println("\t"+cur.getName() + "["+cur.getAdr()+"]");
				Code.loadConst(cur.getAdr());
				Code.put(Code.putstatic);
				Code.put2(sc++);
			}
		}
		
		Code.loadConst(-2);
		Code.put(Code.putstatic);
		Code.put2(sc++);
		this.dataSize = sc;
		
		Code.put(Code.exit);
		Code.put(Code.return_);
		
	}
	
	
	//Mzd nije lep broj polja za ansledjaena polja, npr vrsta je polje 2 kao i b za Kvadar.
	//TODO Problem je kad se poziva metoda na el niza niz[0].met() jer kad se opet ucita design radi se aload
	
	//TODO kad radim new inicijalizujem this
	//generalno je this problem, tj. kad nije eksplicitno naveden
}


