package rs.ac.bg.etf.pp1;

import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class ExtendedTab extends Tab {
	
	public static final Struct setType = new Struct(Struct.Enum),
			boolType = new Struct(Struct.Bool);
	
	
	public static void init() {
		Tab.init();
		//bool type object and struct nodes
		Obj boolObj = Tab.insert(Obj.Type, "bool", boolType);
		boolObj.setAdr(-1);
		boolObj.setLevel(-1);
		
		
		//set type object and struct nodes
		Obj setObj = Tab.insert(Obj.Type, "set", setType);
		setObj.setAdr(-1);
		setObj.setLevel(-1);
		
		
		Obj addMeth = Tab.insert(Obj.Meth, "add", Tab.noType);
		Tab.openScope();
		Obj paramA = Tab.insert(Obj.Var, "a", ExtendedTab.setType); paramA.setLevel(1);
		Obj paramB = Tab.insert(Obj.Var, "b", Tab.intType); paramB.setLevel(1);
		Tab.chainLocalSymbols(addMeth);
		Tab.closeScope();
		addMeth.setLevel(2);
		
		Obj addAllMeth = Tab.insert(Obj.Meth, "addAll", Tab.noType);
		Tab.openScope();
		Obj setA = Tab.insert(Obj.Var, "a", ExtendedTab.setType); setA.setLevel(1);
		Struct arrOfInt = new Struct(Struct.Array, Tab.intType);
		Obj arrB = Tab.insert(Obj.Var, "b", arrOfInt); arrB.setLevel(1);
		Tab.chainLocalSymbols(addAllMeth);
		Tab.closeScope();
		addAllMeth.setLevel(2);
		
	}
	
	public static String StructToString(Struct type) {
		
		if(type == null)return "NULL";
		
		switch (type.getKind()) {
        case Struct.None:
            return "None";
        case Struct.Int:
            return "Int";
        case Struct.Char:
            return "Char";
        case Struct.Array:
        	Struct arrType = type.getElemType();
        	return "Array of "+StructToString(arrType);
        case Struct.Class:
            return "Class";
        case Struct.Bool:
            return "Bool";
        case Struct.Enum:
            return "Set";
        case Struct.Interface:
            return "Interface";
        default:
            return "Unknown";  // Handle unexpected values
		}
	}
	
	
public static String ObjToString(Obj obj) {
		
		if(obj == null)return "NULL";
		
		switch (obj.getKind()) {
        case Obj.NO_VALUE:
            return "None";
        case Obj.Con:
            return "Konstanta";
        case Obj.Var:
            return "Promenljiva";
        case Obj.Type:
            return "Tip";
        case Obj.Fld:
            return "Polje";
        case Obj.Meth:
            return "Metoda/Funkcija";
        case Obj.Prog:
            return "Program";
        case Obj.Elem:
            return "Element?";
        default:
            return "Unknown";  // Handle unexpected values
		}
	}
	
	public static boolean isGlobalScope() {
		return Tab.currentScope.getOuter().getOuter()==null;
	}
}
