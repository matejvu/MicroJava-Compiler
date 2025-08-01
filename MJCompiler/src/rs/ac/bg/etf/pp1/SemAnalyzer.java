package rs.ac.bg.etf.pp1;

import java.util.EmptyStackException;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Stack;

import org.apache.log4j.Logger;


import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class SemAnalyzer extends VisitorAdaptor {
	
	private boolean errorDetected = false;
	private Logger log = Logger.getLogger(getClass());
	
		
	private Obj program;
	private Struct last_type;
	private int last_constant;
	private Struct last_constant_type;
	private boolean isArray = false;
	private Struct extendedType = Tab.noType;
	private Struct new_class = Tab.noType;
	private Obj new_meth =Tab.noObj;
	private int numOfFP = 0;
	private Struct new_interface = Tab.noType;
	private boolean hasReturn = false;
	
	private class Pair<A, B> {
	    public final A first;
	    public final B second;
	    
	    public Pair(A first, B second) {
	        this.first = first;
	        this.second = second;
	    }
	}
	
	private Stack<Struct> designator_struct_stack = new Stack<Struct>();
	private Stack<Obj> designator_obj_stack = new Stack<Obj>();
	
	private boolean inWhileLoop = false;
	private boolean hasAdditionalConstant;
	private boolean noReturnExpr;
	private boolean hasReturnExpr;
	private int numActPars;
	private boolean condActive;
	private boolean isMethInvoked;
	private String last_type_name;
	private boolean podrazumevaniKonstruktor = false;
	private boolean isNeOrEq;
	private boolean mainDeclared = false;
	int nVars;
	
	
	//-------UTILS-------
	

	public void report_error(String message, SyntaxNode info) {
	    errorDetected = true;
	    StringBuilder msg = new StringBuilder(message);
	    int line = (info == null) ? 0 : info.getLine();
	    if (line != 0)
	        msg.append(", na liniji ").append(line);
	    log.error(msg.toString());
	}

	public void report_info(String message, SyntaxNode info) {
	    StringBuilder msg = new StringBuilder(message);
	    int line = (info == null) ? 0 : info.getLine();
	    if (line != 0)
	        msg.append(", na liniji ").append(line);
	    log.info(msg.toString());
	}
	
	public boolean passed() {
		return !errorDetected;
	}
	
	
	
	// Semanticka Analiza
	
	
	
	//-------PROGRAM-------
	
	@Override
	public void visit(Program program) {
		
		nVars = Tab.currentScope.getnVars();
		if(!mainDeclared)report_error("Nije definisana main metoda u programu", program);
		
		Tab.chainLocalSymbols(this.program);
		Tab.closeScope();
	}
	
	@Override
	public void visit(ProgramName progName) {
		program = Tab.insert(Obj.Prog, progName.getI1(), Tab.noType);
		Tab.openScope();
	}
	
	
	//-------TYPE-------
	
	@Override
	public void visit(Type type) {
		Obj typeObj = Tab.find(type.getI1());
		if(typeObj == Tab.noObj) {
			report_error("\'"+type.getI1() + "\' nije validan tip podataka", type);
			last_type = ExtendedTab.noType;
			return;
		}
		if(typeObj.getKind() != Obj.Type) {
			report_error("\'"+type.getI1() + "\' nije ime tipa podataka", type);
			last_type = ExtendedTab.noType;
			return;
		}
//		report_info("Tip: "+typeObj.getName(), type);
		last_type = (Struct) typeObj.getType();
		last_type_name = type.getI1();
		
		//dodato za CG fazu
		type.struct = last_type;
//		lastObj = typeObj;
	}
	
	
	//-------CONSTANT DECLARATIONS-------
	
	
	@Override
	public void visit(ConstChoice_num constChoice_num) {
		this.last_constant = constChoice_num.getN1();
		this.last_constant_type = Tab.intType;
	}
	
	@Override
	public void visit(ConstChoice_bool constChoice_bool) {
		this.last_constant = constChoice_bool.getB1();
		this.last_constant_type = ExtendedTab.boolType;
	}
	
	@Override
	public void visit(ConstChoice_char constChoice_char) {
		this.last_constant = constChoice_char.getC1();
		this.last_constant_type = ExtendedTab.charType;
	}
	
	@Override
	public void visit(ConstList_First constDecl) {
		String name = constDecl.getI1();
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", constDecl);
			return;
		}
		if(last_type==Tab.noType)return;
		if(!last_constant_type.equals(last_type)) {
			report_error("Nemoguca konverzija iz "+ExtendedTab.StructToString(last_constant_type)
			+" u "+ExtendedTab.StructToString(last_type)+" za "+name, constDecl);
			return;
		}
		Obj new_const = Tab.insert(Obj.Con, name, last_type);
		new_const.setAdr(last_constant);
		
		//reset posle obradjenog clana liste
		last_constant = 0;
		last_constant_type = Tab.noType;
	}

	@Override
	public void visit(ConstList_ constList) {
		String name = constList.getI2();
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", constList);
			return;
		}
		if(last_type==Tab.noType)return;
		if(!last_constant_type.equals(last_type)) {
			report_error("Nemoguca konverzija iz "+ExtendedTab.StructToString(last_constant_type)
			+" u "+ExtendedTab.StructToString(last_type)+" za "+name, constList);
			return;
		}
		
		Obj new_const = Tab.insert(Obj.Con, name, last_type);
		new_const.setAdr(last_constant);
		
		//reset posle obradjenog clana liste
		last_constant = 0;
		last_constant_type = Tab.noType;
	}
	
	@Override
	public void visit(ConstDecl constDecl) {
		//reset za kraj niza deklaracija konstanti
		last_type = Tab.noType;
	}
	
	
	//-------VARIABLE DECLARATIONS-------
	
	
	@Override
	public void visit(VarIndexOpt_ index) {
		isArray = true;
	}
	
	@Override
	public void visit(VarList_Type varElem) {
		String name = varElem.getI1();
	
		if((new_class != Tab.noType || new_meth != Tab.noObj || new_interface != Tab.noType)) {
			if( Tab.currentScope.findSymbol(name) != null) {
				report_error("Ime \'"+name+"\' je vec iskorisceno u lokalnom opsegu", varElem);
				return;
			}
		}
		else if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", varElem);
			return;
		}
		if(last_type==Tab.noType)return;
		
		Obj new_var;
		int kind = (new_class!=Tab.noType && new_meth==Tab.noObj) ? Obj.Fld : Obj.Var;
		if(isArray) {
			Struct ArrStruct = new Struct(Struct.Array, last_type);
			
			new_var =  Tab.insert(kind,  name, ArrStruct);
		}
		else {
			new_var =  Tab.insert(kind,  name, last_type);
		}	
		
		//reset posle obradjenog clana liste
		isArray = false;
	}
	
	@Override
	public void visit(VarList_Ident varElem) {
		String name = varElem.getI2();
		if((new_class != Tab.noType || new_meth != Tab.noObj || new_interface != Tab.noType)){
				if( Tab.currentScope.findSymbol(name) != null) {
					report_error("Ime \'"+name+"\' je vec iskorisceno u lokalnom opsegu", varElem);
					return;
				}
		}
		else if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", varElem);
			return;
		}
		if(last_type==Tab.noType)return;
		
		Obj new_var;
		int kind = (new_class!=Tab.noType && new_meth==Tab.noObj) ? Obj.Fld : Obj.Var;
		if(isArray) {
			Struct ArrStruct = new Struct(Struct.Array, last_type);
			
			new_var =  Tab.insert(kind,  name, ArrStruct);
		}
		else {
			new_var =  Tab.insert(kind,  name, last_type);
		}	
		
		//reset posle obradjenog clana liste
		isArray = false;
	}
	
	@Override
	public void visit(VarDecl varElem) {
		//reset za kraj niza deklaracija konstanti
		last_type = Tab.noType;
	}
	
	
	//-------METHOD DECLARATIONS-------
	
	
	@Override
	public void visit(MethodSignature methodSign) {
		if(new_class != Tab.noType || new_interface != Tab.noType)
			Tab.insert(Obj.Var, "this", new_class);
	}
	
	
	@Override
	public void visit(MethodChoice_Type methodChoice) {
		String name = methodChoice.getI2();
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", methodChoice);
			return;
		}
		
		new_meth = Tab.insert(Obj.Meth, name, last_type);
		last_type = Tab.noType;
		new_meth.setLevel(0);
		
		//za CG fazu
		methodChoice.obj = new_meth;
		
		Tab.openScope();
		
//		if(new_class != Tab.noType)
//			Tab.insert(Obj.Var, "this", new_class);
	}
	
	@Override
	public void visit(MethodChoice_Void methodChoice) {
		String name = methodChoice.getI1();
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", methodChoice);
			return;
		}
		
		new_meth = Tab.insert(Obj.Meth, name, Tab.noType);
		last_type = Tab.noType;
		new_meth.setLevel(0);	//da ne treba
		
		//za CG fazu
		methodChoice.obj = new_meth;
		
		Tab.openScope();
		
//		if(new_class != Tab.noType)
//			Tab.insert(Obj.Var, "this", new_class);
	}	
	
	@Override
	public void visit(MethodDecl methodDecl) {
		if(new_interface!=Tab.noType)return;
		if(ExtendedTab.isGlobalScope())return;
		Tab.chainLocalSymbols(new_meth);
		new_meth.setLevel(numOfFP);
		
		
		//mora da ima return
		if(new_meth.getType()!=Tab.noType && !hasReturn) {
			report_error("Metoda \'"+new_meth.getName()+"\' nema definisanu return klauzulu", methodDecl);
		}
		hasReturn=false;
		
		
		Tab.closeScope();
		
		if(Tab.currentScope.getOuter().getOuter() == null && new_meth.getName().equalsIgnoreCase("main")) { 
			mainDeclared  = true;
			if(new_meth.getType() != Tab.noType) report_error("Main metoda ne sme da ima povrtni tip", methodDecl);
			if(new_meth.getLevel() != 0) report_error("Main metoda ne sme da ima formalne argumente", methodDecl);
		}
		
		new_meth = Tab.noObj;
		numOfFP = 0;
	}
	
	
	
	//-------FORMAL PARAMS-------
	
	
	@Override
	public void visit(FormIndexOpt_ formIndex) {
		isArray=true;	
	}
	
	@Override
	public void visit(FormTypeList_Epsilon formTypeList) {
		String name = formTypeList.getI2();
		if(Tab.currentScope.findSymbol(name) != null) {
			report_error("AIme \'"+name+"\' je vec iskorisceno", formTypeList);
			return;
		}
		
		if(last_type==Tab.noType)return;
		
		Obj new_var;
		if(isArray) {
			Struct ArrStruct = new Struct(Struct.Array, last_type);
			
			new_var =  Tab.insert(Obj.Var,  name, ArrStruct);
		}
		else {
			new_var =  Tab.insert(Obj.Var,  name, last_type);
		}	
		
		new_var.setFpPos(1); //jer je formalni param
		isArray=false;
		numOfFP++;
		
	}
	
	@Override
	public void visit(FormTypeList_ formTypeList) {
		String name = formTypeList.getI3();
		if(Tab.currentScope().findSymbol(name) != null) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", formTypeList);
			return;
		}
		
		if(last_type==Tab.noType)return;
		
		Obj new_var;
		if(isArray) {
			Struct ArrStruct = new Struct(Struct.Array, last_type);
			
			new_var =  Tab.insert(Obj.Var,  name, ArrStruct);
		}
		else {
			new_var =  Tab.insert(Obj.Var,  name, last_type);
		}	
		
		new_var.setFpPos(1); //jer je formalni param
		isArray=false;
		numOfFP++;
		
	}
	
	
	//-------CLASS DECLARATIONS-------
	
	
	@Override
	public void visit(ClassHeader classHeader) {
		String name = classHeader.getI1();
		
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", classHeader);
			return;
		}
		
//		report_info("Klasa "+ name+ " sa je dodata!", classHeader);
		new_class = new Struct(Struct.Class);
		Obj classObj = Tab.insert(Obj.Type, name, new_class);
		
		Tab.openScope();
		
		//dodato za CG fazu
		Obj tvf_pointerObj = Tab.insert(Obj.Fld, "_tvf_", Tab.noType);
		//dodato za CG fazu
		classHeader.obj = classObj;
		
		if(extendedType == Tab.noType)return;
		
		if(extendedType.getKind() == Struct.Class) { new_class.setElementType(extendedType); } //return izbacen
		if(extendedType.getKind() == Struct.Interface) { new_class.addImplementedInterface(extendedType); return; }
		if(extendedType.getKind() != Struct.Class && extendedType.getKind() != Struct.Interface) {
			report_error("Izvodjenje nije moguce iz: \'"+ExtendedTab.StructToString(extendedType)+"\'", classHeader);
			return;
		}
		
		
		//dodatak za CG da bi se nasledjivanje uradilo u napred
		Struct parent_class = new_class.getElemType();
		
		if(parent_class != Tab.noType && parent_class != null) {
			Iterator<Obj> parent_flds = parent_class.getMembers().iterator();
			while(parent_flds.hasNext()) {
				Obj cur = parent_flds.next();
				if(cur.getKind() != Obj.Fld)continue;
				if(Tab.currentScope.findSymbol(cur.getName())==null) {
//					Ubacivanje nasledjenih metoda i polja
					Obj inheritedMeth = Tab.insert(cur.getKind(), cur.getName(), cur.getType());
					//dodato za CG fazu
					if(inheritedMeth.getKind() == Obj.Meth)inheritedMeth.setAdr(-1);
				}	
			}
		}
		
		
	}

	@Override
	public void visit(ClassDecl classDecl) {
		
		if(ExtendedTab.isGlobalScope())return;
		
		
		//provera da li implementira ne implementirane metode interfejsa
		Iterator<Struct> interfaceIterator = new_class.getImplementedInterfaces().iterator();
		if(interfaceIterator.hasNext()) {
			Iterator<Obj> methodIterator = interfaceIterator.next().getMembers().iterator();
			while(methodIterator.hasNext()) {
				Obj meth = methodIterator.next(); //methoda interfejsa
				if(meth.getFpPos() == 0) {
					
					if(Tab.currentScope.findSymbol(meth.getName())==null) {
//						Ubacivanje nasledjenih metoda i polja
						Obj inheritedMeth = Tab.insert(meth.getKind(), meth.getName(), meth.getType());
						//dodato za CG fazu
						if(inheritedMeth.getKind() == Obj.Meth)inheritedMeth.setAdr(-1);
					}
					
					continue;}
				
				String signMethName = meth.getName();
				if(Tab.currentScope.findSymbol(signMethName)==null) {
					report_error("Nije implementirana metoda \'"+signMethName+"\' deklarisana interfejsom", classDecl);
					break;
				}
				Obj implMeth = Tab.currentScope.findSymbol(signMethName);
				Iterator<Obj>varIterator = implMeth.getLocalSymbols().iterator();
				
				
				//TODO Proveriti parametre metoda da li s epoklapaju tipski
			}
		}
		
		//nasledjivanje metoda i polja
		Struct parent_class = new_class.getElemType();
		
		if(parent_class != Tab.noType && parent_class != null) {
			Iterator<Obj> parent_flds = parent_class.getMembers().iterator();
			while(parent_flds.hasNext()) {
				Obj cur = parent_flds.next();
				if(Tab.currentScope.findSymbol(cur.getName())==null) {
//					Ubacivanje nasledjenih metoda i polja
					Obj inheritedMeth = Tab.insert(cur.getKind(), cur.getName(), cur.getType());
					//dodato za CG fazu
					if(inheritedMeth.getKind() == Obj.Meth)inheritedMeth.setAdr(-1);
				}
				
			}
			
		}
			

		
		
		Tab.chainLocalSymbols(new_class);
		
		Tab.closeScope();
		
		new_class = Tab.noType;
		
		
	}
	
	@Override
	public void visit(ClasExtendOpt_ classExtend) {
		
//		report_info("Extended class: "+classExtend.ge, classExtend);
		extendedType = last_type;
		last_type = Tab.noType;
	}
	
	
	//-------INTERFACE DECLARATIONS-------
	
	
	@Override
	public void visit(InterfaceHeader interfaceHeader) {
		String name = interfaceHeader.getI1();
		
		if(Tab.find(name) != Tab.noObj) {
			report_error("Ime \'"+name+"\' je vec iskorisceno", interfaceHeader);
			return;
		}
		
		new_interface = new Struct(Struct.Interface);
		Obj interfaceObj = Tab.insert(Obj.Type, name, new_interface);
		
		Tab.openScope();
	}
	
	@Override
	public void visit(InterfaceDecl interfaceDecl) {
		
//		if(ExtendedTab.isGlobalScope())return;
		Tab.chainLocalSymbols(new_interface);

		Tab.closeScope();
		new_interface = Tab.noType;
	}
	
	@Override
	public void visit(InterfaceMethodList_Decl methodDecl) {
		if(ExtendedTab.isGlobalScope())return;
		new_meth.setFpPos(0); 		//Oznaka da je implementirana
		Tab.chainLocalSymbols(new_meth);
		new_meth.setLevel(numOfFP);
		
		Tab.closeScope();
		new_meth = Tab.noObj;
		numOfFP = 0;
	}
	
	@Override
	public void visit(InterfaceMethodList_Signature methodSign) {
		if(ExtendedTab.isGlobalScope())return;
		new_meth.setFpPos(-1); 		//Oznaka da je samo potpis
		Tab.chainLocalSymbols(new_meth);
		new_meth.setLevel(numOfFP);
		
		Tab.closeScope();
		new_meth = Tab.noObj;
		numOfFP = 0;
	}
	
	
	//-------STATEMENT RETURN-------
	
	
//	@Override
//	public void visit(Statement_Return statementReturn) {
//		hasReturn = true;
//	}
	
	
	//-------DESIGANTOR DECLARATIONS-------
	
	private Pair<Struct, Obj> popDecl() {	
		Struct struct;
		Obj obj;
		try{
			struct = designator_struct_stack.pop();
			
		}
		catch (EmptyStackException e) { 
			struct = Tab.noType;
		}
		try{
			obj = designator_obj_stack.pop();
		}
		catch (EmptyStackException e) { 
			obj = Tab.noObj;
		}
		return new Pair<>(struct, obj);
	}
	
	private void pushDecl(Struct struct, Obj obj) {
		struct = (struct == null) ? new Struct(Struct.None) : struct;
		obj = (obj == null) ? new Obj(Obj.NO_VALUE, "dummy", struct) : obj;
		
		designator_struct_stack.push(struct);
		designator_obj_stack.push(obj);
	}
	
	@Override
	public void visit(DesignatorList_Ident designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct type = result.first;
		Obj object = result.second;
		
//		report_info("DOT ident se dodaje na: "+object.getName()+"["+ExtendedTab.StructToString(type)+"]", designator);
		if(type.getKind() != Struct.Class && type.getKind() != Struct.Interface) {
			report_error("\'"+object.getName()+"\' nema polja jer je "+ExtendedTab.StructToString(type), designator);
			return;
		}
		
		
		Obj cur = null, res = null;
		Iterator<Obj> fldIterator = type.getMembers().iterator();
		while(fldIterator.hasNext()) {
			cur = fldIterator.next();
			if(cur.getName().equals(designator.getI2())) {
				res = cur;
				break;
			}
		}
		
		if(new_class != Tab.noType || new_interface != Tab.noType) {
			res = Tab.currentScope().getOuter().findSymbol(designator.getI2()); //dodato getOuter!!
		}
		
		//da li je nadjeno
		if(res == null || res == Tab.noObj) {
			report_error("Ne postoji polje sa imenom \'"+designator.getI2()+"\'", designator);
			return;
		}
		//VLJd resoeno sa Epsilon smenom za ()  "todo STA SE DESAV SA METODAMA klasaa-??"

		
		pushDecl(res.getType(), res);
		
		//dodato za CG fazu
		designator.obj = res;
//		designator_type = Dot;
	}
	
	@Override
	public void visit(DesignatorList_Expr designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct indexS = result.first;
		Obj indexO = result.second;
		
		result = popDecl();
		Struct declS = result.first;
		Obj declO = result.second;
		
		
		
		
		if(indexS.getKind() != Struct.Int) {
			report_error("Ne moze da se indeksira sa "+ExtendedTab.StructToString(indexS), designator);
			return;
		}
		
		if(declS.getKind() != Struct.Array) {
			report_error("\'"+declO.getName()+"\' ne moze da se indeksira jer je "+ExtendedTab.StructToString(declS), designator);
			return;
		}
		
		Obj dummy = new Obj(Obj.Elem, "dummy_elem", declS.getElemType());
//		pushDecl(declS.getElemType(), Tab.noObj);//todo dummy obj umeesto noobj
		pushDecl(declS.getElemType(), dummy);//todo dummy obj umeesto noobj
	
		//dodato za CG fazu
		designator.obj = dummy;
	}
		
//		designator_type = Breket;
//	@Override
//	public void visit(DesignatorLBrack designator) {
//		pushDecl();
//		current_designator = Tab.noObj;
//		current_designator_struct = Tab.noType;
//	}
	
	
	
	@Override
	public void visit(DesignatorList_Epsilon designator) {
		
		
		String name = designator.getI1();
		Obj new_obj = Tab.find(name);
		Struct new_struct = new_obj.getType();
//		System.out.println("IDENT: "+new_obj.getName()+ExtendedTab.ObjToString(new_obj));
		if(new_obj == Tab.noObj) {
			report_error("Ime \'"+name+"\' nije deklarisano", designator);
			return;
		}
		pushDecl(new_struct, new_obj);
		
		//dodato za CG fazu
		designator.obj = new_obj;
//		designator_type = Ident;
		
	}

	
	//-------DESIGANTOR STATEMENTS-------
	
	
//	@Override
//	public void visit(LeftSideDesignatorStatement designator) {
//		left_side_struct = current_designator_struct;
//		left_side_obj = current_designator;
//		pushDecl();
//	}
	
	@Override
	public void visit(DesignatorChoice_Assignop designator) {
		
		Pair<Struct, Obj> result = popDecl();
		Struct current_expr = result.first;
		Obj current_expr_obj = result.second;
		result = popDecl();
		Struct  left_side_struct = result.first;
		Obj left_side_obj = result.second;
				
		if(left_side_obj.getKind() != Obj.Var && left_side_obj.getKind() != Obj.Fld && left_side_obj.getKind() != Obj.Elem) {
			report_error("Nije promenljiva sa leve strane jednakosti vec "+ExtendedTab.ObjToString(left_side_obj), designator);
			return;
		}
		
		if(current_expr.getKind()==Struct.Class) {
			Struct implInterface;
			try {
				implInterface = current_expr.getImplementedInterfaces().iterator().next();
			}
			catch (NoSuchElementException e){
				implInterface = Tab.noType;
			}
			Struct parentClass = current_expr.getElemType();
			while(parentClass != Tab.noType || implInterface != Tab.noType) {
				if(implInterface != Tab.noType && left_side_struct == implInterface) { current_expr = implInterface; break; }
				if(parentClass != null && left_side_struct == parentClass) { current_expr = parentClass; break; }
				if(parentClass != null) parentClass = parentClass.getElemType();
				if(parentClass == Tab.noType || parentClass == null)break;
				try { implInterface = parentClass.getImplementedInterfaces().iterator().next(); }
				catch (NoSuchElementException e){ implInterface = Tab.noType; }
			}
		}
			
		//kompatibilnost sa expr
		if(!current_expr.assignableTo(left_side_struct)) {
			report_error("Nije moguce dodeliti "+ExtendedTab.StructToString(current_expr)
			+" u promenljivu tipa "+ExtendedTab.StructToString(left_side_struct), designator);
			return;
		}
		
		
	}
	
	@Override
	public void visit(DesignatorChoice_Inc designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct  left_side_struct = result.first;
		Obj left_side_obj = result.second;
		
		if(left_side_obj.getKind() != Obj.Var && left_side_obj.getKind() != Obj.Fld && left_side_obj.getKind() != Obj.Elem) {
			report_error("Nije promenljiva sa leve strane jednakosti vec "+ExtendedTab.ObjToString(left_side_obj), designator);
			return;
		}
		
				
		if(left_side_struct.getKind() != Struct.Int) {
			report_error("Operator \'++\' nije moguce primeniti na tipu "+ExtendedTab.StructToString(left_side_struct), designator);
			return;
		}
	}
	
	@Override
	public void visit(DesignatorChoice_Dec designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct  left_side_struct = result.first;
		Obj left_side_obj = result.second;
		
		if(left_side_obj.getKind() != Obj.Var && left_side_obj.getKind() != Obj.Fld && left_side_obj.getKind() != Obj.Elem) {
			report_error("Nije promenljiva sa leve strane jednakosti vec"+ExtendedTab.ObjToString(left_side_obj), designator);
			return;
		}
		
		if(left_side_struct.getKind() != Struct.Int) {
			report_error("Operator \'--\' nije moguce primeniti na tipu "+ExtendedTab.StructToString(left_side_struct), designator);
			return;
		}
	}
	
	@Override
	public void visit(DesignatorChoice_ActPars designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct  left_side_struct = result.first;
		Obj left_side_obj = result.second;
		
		if(left_side_obj.getKind() != Obj.Meth) {
			report_error("\'"+left_side_obj.getName()+"\' nije ime metode vec "+ExtendedTab.ObjToString(left_side_obj), designator);
			return;
		}
	}
	
//	@Override
//	public void visit(FirstSet designator) {
//
//		
//		right_side_obj = current_designator; 
//		right_side_struct = current_designator_struct;
//		pushDecl();
//	}
	
	@Override
	public void visit(Designator_Designator designator) {
		Pair<Struct, Obj> result = popDecl();
		Struct  current_designator_struct = result.first;
		Obj current_designator = result.second;
		
		result = popDecl();
		Struct  right_side_struct = result.first;
		Obj right_side_obj = result.second;
		
		result = popDecl();
		Struct  left_side_struct = result.first;
		Obj left_side_obj = result.second;
		
		if(right_side_struct.getKind() != Struct.Enum) {
			report_error("Prvi operand \'"+right_side_obj.getName()+"\' nije set vec "+ExtendedTab.StructToString(right_side_struct), designator);
//			return;
		}
		
		if(current_designator_struct.getKind() != Struct.Enum) {
			report_error("Drugi operand \'"+current_designator.getName()+"\' nije set vec "+ExtendedTab.StructToString(current_designator_struct), designator);
//			return;
		}
		
		if(left_side_struct.getKind() != Struct.Enum) {
			report_error("Odredisni operand \'"+left_side_obj.getName()+"\' nije set vec "+ExtendedTab.StructToString(left_side_struct), designator);
//			return;
		}
	}
	
	
	//-------STATEMENTS-------
	
	
	@Override
	public void visit(Statement_Break statement) {
		if(!inWhileLoop) {
			report_error("Iskoriscen break izvan do while petlje", statement);
			return;
		}
	}
	
	@Override
	public void visit(Statement_Continue statement) {
		if(!inWhileLoop) {
			report_error("Iskoriscen continue izvan do while petlje", statement);
			return;
		}
	}
	
	@Override
	public void visit(DoWhileBegin statement) {
		inWhileLoop = true;
	}
	
	@Override
	public void visit(Statement_Read statement) {
		Pair<Struct, Obj> result = popDecl();
		Struct  current_designator_struct = result.first;
		Obj current_designator = result.second;
		
		if(current_designator.getKind() != Obj.Var
				&& current_designator.getKind() != Obj.Fld
				&& current_designator.getKind() != Obj.Elem) {
				
			report_error("Nije moguce uraditi read nad "+ExtendedTab.ObjToString(current_designator), statement);
			return;
		}
		if(current_designator_struct.getKind() != Struct.Int
			&& current_designator_struct.getKind() != Struct.Char
			&& current_designator_struct.getKind() != Struct.Bool) {
			
			report_error("Nije moguce uraditi read sa tipom "+ExtendedTab.StructToString(current_designator_struct), statement);
			return;
		}
	}
	
	@Override
	public void visit(Statement_Print statement) {
		
		Pair<Struct, Obj> result; 
		result = popDecl();
		Struct  current_designator_struct = result.first;
		Obj current_designator = result.second;
		
		//vljd ne treba nista da se radi//"todo sta je sa numCOnst pri ispisu? 'StatementNumOpt_' "
		
		if(current_designator.getKind() != Obj.Var
				&& current_designator.getKind() != Obj.Fld
				&& current_designator.getKind() != Obj.Con
				&& current_designator.getKind() != Obj.Elem) {
				
			report_error("Nije moguce uraditi print nad "+ExtendedTab.ObjToString(current_designator), statement);
			return;
		}
		if(current_designator_struct.getKind() != Struct.Int
			&& current_designator_struct.getKind() != Struct.Char
			&& current_designator_struct.getKind() != Struct.Bool
			&& current_designator_struct.getKind() != Struct.Enum) {
			
			report_error("Nije moguce uraditi print sa tipom "+ExtendedTab.StructToString(current_designator_struct), statement);
			return;
		}
	}
	
	@Override
	public void visit(StatementExprOpt_ option) {
		hasReturnExpr = true;
	}
	
	@Override
	public void visit(Statement_Return statement) {
		hasReturn = true;
		if(new_meth == Tab.noObj) {
			report_error("Koriscenje return van metode nije dozvoljeno", statement);
			return;
		}
		if(!hasReturnExpr)return;
			
		
		hasReturnExpr = false;
		Pair<Struct, Obj> result; 
		result = popDecl();
		Struct  current_designator_struct = result.first;
		
		if(new_meth.getType().getKind()==Struct.None) {
			report_error("Void metoda ne moze da ima povratnu vrednost tipa "+ExtendedTab.StructToString(new_meth.getType()), statement);
			return;
		}
		if(new_meth.getType().getKind() != current_designator_struct.getKind()) {
			report_error("Tip "+ExtendedTab.StructToString(current_designator_struct)+" se ne poklapa sa povratnim tipom metode "
							+ExtendedTab.StructToString(new_meth.getType()), statement);
			return;
		}	
	}
	
	@Override
	public void visit(IfCondition statement) {
		Pair<Struct, Obj> result = popDecl();
		Struct  condition_struct = result.first;
		Obj condition_object = result.second;
		
		if(condition_struct.getKind() != Struct.Bool || !condActive) {
			System.out.println(condActive);
			System.out.println(condition_object.getName());
			System.out.println(ExtendedTab.StructToString(condition_struct));
			report_error("Uslov If iskaza ne moze biti tipa "+ExtendedTab.StructToString(condition_struct), statement);
		}
		condActive = false;
	}
	
	@Override
	public void visit(StatementConditionOpt_ statement) {
		Pair<Struct, Obj> result = popDecl();
		Struct  condition_struct = result.first;
		//unutar do while statementa, pretpostavka da je razresen designatorStatement
		
		if(condition_struct.getKind() != Struct.Bool || !condActive) {
			report_error("Uslov Do while iskaza ne moze biti tipa "+ExtendedTab.StructToString(condition_struct), statement);
		}
		condActive = false;
		inWhileLoop = false;
	}
	
	
	//-------ACTUAL PARAMETERS-------
	
	
	@Override
	public void visit(ActPars_Epsilon actPars) {
		//na steku je (prvi)expr a ispod njega je designator koji oznacava meth
		numActPars=1;
		Pair<Struct, Obj> result = popDecl();
		Struct expr_struct = result.first;
		Obj expr_obj = result.second;
		
		result = popDecl();
		Struct meth_struct = result.first;
		Obj meth_obj = result.second;
		pushDecl(meth_struct, meth_obj);
		
		if(meth_obj.getKind() != Obj.Meth) {
			report_error("Designator "+meth_obj.getName()+"nije metoda/funkcija", actPars);
			return;
		}
		
		if(meth_obj.getLevel()<numActPars) {
			report_error("Predato je vise parametara nego sto "+meth_obj.getName()+" definise", actPars);
			return;
		}
		
		Iterator<Obj> fp_iterator = meth_obj.getLocalSymbols().iterator();
		int counter=0;
		while(fp_iterator.hasNext()) {
			Obj cur = fp_iterator.next();
			if(cur.getFpPos()==1)counter++;
			
			if(counter == numActPars) {
				if(!expr_struct.assignableTo(cur.getType())) {
					report_error("Tip " + ExtendedTab.StructToString(expr_struct)
								+ " ne moze biti predat kao parametar "
								+ ExtendedTab.StructToString(cur.getType()), actPars);
					return;
				}
					
				break;
			}
		}
	}
	
	@Override
	public void visit(ActPars_ actPars) {
		//na steku je sledeci expr a ispod njega je designator koji oznacava meth
		numActPars++;
		Pair<Struct, Obj> result = popDecl();
		Struct expr_struct = result.first;
		Obj expr_obj = result.second;
		
		result = popDecl();
		Struct meth_struct = result.first;
		Obj meth_obj = result.second;
		pushDecl(meth_struct, meth_obj);
		
		if(meth_obj.getKind() != Obj.Meth) {
			report_error("Designator "+meth_obj.getName()+"nije metoda/funkcija", actPars);
			return;
		}
		
		if(meth_obj.getLevel()<numActPars) {
			report_error("Predato je vise parametara nego sto "+meth_obj.getName()+" definise", actPars);
			return;
		}
		
		Iterator<Obj> fp_iterator = meth_obj.getLocalSymbols().iterator();
		int counter=0;
		while(fp_iterator.hasNext()) {
			Obj cur = fp_iterator.next();
			if(cur.getFpPos()==1)counter++;
			
			if(counter == numActPars) {
				if(!expr_struct.assignableTo(cur.getType())) {
					report_error("Tip " + ExtendedTab.StructToString(expr_struct)
								+ " ne moze biti predat kao parametar "
								+ ExtendedTab.StructToString(cur.getType()), actPars);
					return;
				}
					
				break;
			}
		}
	}
	
	@Override
	public void visit(ActParsOpt_ actPars) {
		
		Pair<Struct, Obj> result = popDecl();
		Struct meth_struct = result.first;
		Obj meth_obj = result.second;
		pushDecl(meth_struct, meth_obj);
		if(numActPars < meth_obj.getLevel()) {
			report_error("Predato je "+numActPars+" umesto "+meth_obj.getLevel()
						+" koliko propisuje "+meth_obj.getName(), actPars);
		}
		
		numActPars=0;
	}
	
//	@Override
//	public void visit(ActParsOpt_Epsilon actPars) {
//		
//		Pair<Struct, Obj> result = popDecl();
//		Struct meth_struct = result.first;
//		Obj meth_obj = result.second;
//		pushDecl(meth_struct, meth_obj);
//		
//		
//		numActPars=0;
//	}
	
	
	//-------CONDITION DECLARATIONS-------
	
	
	@Override
	public void visit(CondFactExprOpt_Epsilon condFact) {
		
		Struct meth_struct = Tab.noType;
		Obj meth_obj = Tab.noObj;
		
		pushDecl(meth_struct, meth_obj);
	}
	
	@Override
	public void visit(CondFact condFact) {
		Pair<Struct, Obj> result = popDecl();
		Struct expr2_struct = result.first;
		Obj expr2_obj = result.second;
		result = popDecl();
		Struct expr1_struct = result.first;
		Obj expr1_obj = result.second;
		
		if(expr2_obj == Tab.noObj && expr2_struct == Tab.noType) {
			if(expr1_struct.getKind() != Struct.Bool) {
				report_error("Faktor uslova \'"+expr1_obj.getName()+"\' mora da bude bool", condFact);				
				return; //da li treba je pitanje
			}
		}
		else if(!expr1_struct.compatibleWith(expr2_struct)) {
			report_error("Tipovi "+ExtendedTab.StructToString(expr1_struct)+" i "
						+ExtendedTab.StructToString(expr2_struct)+" nisu kompatibilni", condFact);
			return;
		}
		
		//todo Za != i == moraju kod klasa, vrv ce biti uradjeno u Relop
		if((expr1_struct.getKind() == Struct.Class && expr2_struct.getKind() == Struct.Class)
					 || (expr1_struct.getKind() == Struct.Array || expr2_struct.getKind() == Struct.Array)) {
			if(!isNeOrEq) {
				report_error("Nije moguce koristi taj relacioni operator sa tipom "+ExtendedTab.StructToString(expr1_struct), condFact);
				return;
			}
			isNeOrEq = false;
		}
		
		if(!condActive) {
			Obj pomBool = new Obj(Obj.Con, "dummy_bool", ExtendedTab.boolType);
			pushDecl(ExtendedTab.boolType, pomBool);
			condActive = true;
		}
		
	}
		
	
	//-------EXPR DECLARATIONS-------
	
	
	@Override
	public void visit(FactorOpt_Minus factorOpt) {
		Pair<Struct, Obj> result = popDecl();
		Struct factor_struct = result.first;
		Obj factor_obj = result.second;
		
		if(factor_struct.getKind() != Struct.Int) {
			report_error("Operator \'-\' ne moze da se primeni na tipu "+ExtendedTab.StructToString(factor_struct), factorOpt);
		}
		pushDecl(factor_struct, factor_obj);
		
	}
	
	@Override
	public void visit(ExprTermList_ exprTerm) {
		Pair<Struct, Obj> result = popDecl();
		Struct term2_struct = result.first;
		Obj term2_obj = result.second;
		
		result = popDecl();
		Struct term1_struct = result.first;
		Obj term1_obj = result.second;
		
		if(term1_struct.getKind() != Struct.Int || term2_struct.getKind() != Struct.Int) {
			report_error("Tipovi "+ExtendedTab.StructToString(term1_struct)+" i "
					+ExtendedTab.StructToString(term2_struct)+" nisu pogodni za Addop", exprTerm);
		}
		
		//nijie bitno koji, bitno je da se propagira info o int-u
		pushDecl(term1_struct, term1_obj);
		
	}
	
	//Dodato za CG fazu
	@Override
	public void visit(Expr_Term exprTerm) {
		Pair<Struct, Obj> result = popDecl();
		Struct struct = result.first;
		Obj obj = result.second;
		pushDecl(struct, obj);
		
		exprTerm.struct = struct;		
	}
	
	
	@Override
	public void visit(TermFactorList_ termFactor) {
		Pair<Struct, Obj> result = popDecl();
		Struct term2_struct = result.first;
		Obj term2_obj = result.second;
		
		result = popDecl();
		Struct term1_struct = result.first;
		Obj term1_obj = result.second;
		
		if(term1_struct.getKind() != Struct.Int || term2_struct.getKind() != Struct.Int) {
			report_error("Tipovi "+ExtendedTab.StructToString(term1_struct)+" i "
					+ExtendedTab.StructToString(term2_struct)+" nisu pogodni za Mulop", termFactor);
		}
		
		//nijie bitno koji, bitno je da se propagira info o int-u
		pushDecl(term1_struct, term1_obj);
		
	}
	
	@Override
	public void visit(Expr_Map exprMap) {
		Pair<Struct, Obj> result = popDecl();
		Struct term2_struct = result.first;
		Obj term2_obj = result.second;
		
		result = popDecl();
		Struct term1_struct = result.first;
		Obj term1_obj = result.second;
		
		//prvi designator
		if(term1_obj.getKind() != Obj.Meth) report_error("\'"+term1_obj.getName()+"\' nije funkcija", exprMap);	
		if(term1_obj.getLevel() != 1) report_error("\'"+term1_obj.getName()+"\' ne prima 1 argument vec "+term1_obj.getLevel(), exprMap);
		if(term1_struct.getKind() != Struct.Int) report_error("\'"+term1_obj.getName()+"\' nema povratnu vrednost Int", exprMap);
		Iterator<Obj> arg_iter = term1_obj.getLocalSymbols().iterator();
		boolean ima = false;
		while(arg_iter.hasNext()) {
			Obj cur = arg_iter.next();
			if(cur.getFpPos()==1) {
				if(cur.getType().getKind() == Struct.Int)ima = true;
				break;
			}
		}
		if(!ima)report_error("Argument prve funkcije nije tipa Int", exprMap);
		
		//drugi designator
		if(term2_struct.getKind()!=Struct.Array)report_error("Drugi operand nije niz vec "+ExtendedTab.StructToString(term2_struct), exprMap);
		else if(term2_struct.getElemType().getKind() != Struct.Int) report_error("Drugi operand je "+ExtendedTab.StructToString(term2_struct), exprMap);
		
		Obj sum_dummy = new Obj(Obj.Var, "map_sum_dummy", Tab.intType);
		
		//bitno je da se propagira info o int-u
		pushDecl(Tab.intType, sum_dummy);
		
		//dodato za CG fazu
		exprMap.struct = sum_dummy.getType();
	}
	
	
	//-------FACTOR-------
	
	@Override
	public void visit(Factor_Number factor) {
		Obj dummy = new Obj(Obj.Con, "dummy", Tab.intType);
		pushDecl(Tab.intType, dummy);
	}
	
	@Override
	public void visit(Factor_Character factor) {
		Obj dummy = new Obj(Obj.Con, "dummy", Tab.charType);
		pushDecl(Tab.charType, dummy);
	}
	
	@Override
	public void visit(Factor_Bool factor) {
		Obj dummy = new Obj(Obj.Con, "dummy", ExtendedTab.boolType);
		pushDecl(ExtendedTab.boolType, dummy);
	}
	
	@Override
	public void visit(FactorDesignatorOpt_ factor) {
		//moze jer je tacno pred obradu 'Factor_Designator' tj. ne moze ulancavanju da smeta
		isMethInvoked = true;	
		
		Pair<Struct, Obj> result = popDecl();
		Struct meth_struct = result.first;
		Obj meth_obj = result.second;
//		pushDecl(meth_struct, meth_obj);
//		System.err.println("Fija: "+meth_obj.getName()+" sa povr tipom: "+ExtendedTab.StructToString(meth_struct));

		if(meth_obj.getKind() != Obj.Meth) {
			report_error("Nije moguce pozvati \'"+meth_obj.getName()+"\' jer nije funkcija", factor);
			pushDecl(meth_struct, meth_obj);return;
		}
		
		Obj return_dummy = new Obj(Obj.Var, "return_dummy", meth_obj.getType());
		pushDecl(meth_obj.getType(), return_dummy);

	}
	
	@Override
	public void visit(FactorDesignatorOpt_Epsilon factor) {
		Pair<Struct, Obj> result = popDecl();
		Struct struct = result.first;
		Obj obj = result.second;
		pushDecl(struct, obj);
		
		if(obj.getKind() == Obj.Meth) {
			report_error("Nisu navedene ( ) nakon imena metode \'"+obj.getName()+"\'", factor);
		}
	}
	
	//dodato za CG fazu
	@Override
	public void visit(Factor_Designator factor) {
		Pair<Struct, Obj> result = popDecl();
		Struct struct = result.first;
		Obj obj = result.second;
		pushDecl(struct, obj);
		
		factor.obj = obj;
	}
	
	
	//-------FACTOR NEW-------
	
	@Override
	public void visit(FactorNewChoice_Expr factor) {
		Pair<Struct, Obj> result = popDecl();
		Struct expr_struct = result.first;
		Obj expr_obj = result.second;
		
		
		if(last_type == Tab.noType) report_error("Nije lepo definisan tip pri new iskazu", factor);
		if(expr_struct.getKind() != Struct.Int) report_error("Izraz u [] mora biti Int a ne "+ExtendedTab.StructToString(expr_struct), factor);
		
		Obj obj;
		if(last_type == ExtendedTab.setType) {
			obj = new Obj(Obj.Var, "dummy_set", ExtendedTab.setType);
		}
		else {
			Struct arr_struct = new Struct(Struct.Array);
			arr_struct.setElementType(last_type);
			obj = new Obj(Obj.Var, "dummy_arr", arr_struct);
		}
		pushDecl(obj.getType(), obj);
	}
	
	@Override
	public void visit(FactorNewChoice_ActPars factor) {
		
		if(last_type == Tab.noType) report_error("Nije lepo definisan tip pri new iskazu", factor);
		
		if(podrazumevaniKonstruktor) {
			Obj obj = new Obj(Obj.Var, "dummy_new", last_type);//var ili con??
			pushDecl(last_type, obj);
			podrazumevaniKonstruktor = false;
		}
//		pushDecl(obj.getType(), obj);
		
	}
	
	@Override
	public void visit(LParenFactorNewChoice lParenFactor) {
		if(last_type.getKind() != Struct.Class) report_error("Tip new iskaza nije korisnicki definisan tip vec "+ExtendedTab.StructToString(last_type), lParenFactor);
		Iterator<Obj> class_iter = last_type.getMembers().iterator();
		boolean ima=false;
		while(class_iter.hasNext()) {
			Obj cur = class_iter.next();
			if(cur.getKind() != Obj.Meth)continue;
			if(cur.getName().equals(last_type_name)) {
				pushDecl(cur.getType(), cur);
				ima = true;
				break;
			}
		}
		if(!ima) {
			podrazumevaniKonstruktor = true;
//			report_error("Klasa "+last_type_name+" nema definisan konsturktor", lParenFactor);
//			pushDecl(Tab.noType, Tab.noObj);
		}
	}
	
	
	//
	
	
	@Override
	public void visit(Relop_Eq relop) {
		isNeOrEq = true;
	}
	
	@Override
	public void visit(Relop_Ne relop) {
		isNeOrEq = true;
	}
	
}
