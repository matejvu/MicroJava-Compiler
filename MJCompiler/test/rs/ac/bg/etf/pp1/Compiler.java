package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

import java_cup.runtime.Symbol;

import org.apache.log4j.Logger;
import org.apache.log4j.xml.DOMConfigurator;


import rs.ac.bg.etf.pp1.ast.Program;
import rs.ac.bg.etf.pp1.SemAnalyzer;
import rs.ac.bg.etf.pp1.util.Log4JUtils;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Scope;
import rs.etf.pp1.symboltable.concepts.Struct;

public class Compiler {

	static {
		DOMConfigurator.configure(Log4JUtils.instance().findLoggerConfigFile());
		Log4JUtils.instance().prepareLogFile(Logger.getRootLogger());
	}
	
	public static void main(String[] args) throws Exception {
		
		Logger log = Logger.getLogger(Compiler.class);
		
		Reader br = null;
		try {
			File sourceCode = new File("test/program.mj");
			log.info("Compiling source file: " + sourceCode.getAbsolutePath());
			
			br = new BufferedReader(new FileReader(sourceCode));
			Yylex lexer = new Yylex(br);
			
			//formiranje tabele simbola
			MJParser p = new MJParser(lexer);
	        Symbol s = p.parse();  //pocetak parsiranja
	        
	        Program prog = (Program)(s.value);

			// ispis sintaksnog stabla
//			log.info(prog.toString(""));
			log.info("===================================");
			
			
			//inicijalizacija tabele simbola
			Tab.init();
			
			
			//semanticka analiza
			SemAnalyzer sa = new SemAnalyzer();
			ExtendedTab.init();
			prog.traverseBottomUp(sa);
			
			//ispis tabele simbola
			log.info("===================================");
			Tab.dump();
			
//			// ispis prepoznatih programskih konstrukcija

//
//			log.info("===================================");
//
//			MyDumpSymbolTableVisitor visitor = new MyDumpSymbolTableVisitor();
//			Tab.dump(visitor);

			if(!p.errorDetected && sa.passed()){
				
				//Genereisanje koda
				File objFile = new File("test/program.obj");
				if(objFile.exists()) objFile.delete();
				
				CodeGenereator cg = new CodeGenereator();
				cg.init();
				prog.traverseBottomUp(cg);
				Code.dataSize = cg.getDataSize();
				Code.mainPc = cg.getMainPc();
				Code.write(new FileOutputStream(objFile));
				
				
				log.info("Generisanje uspesno zavrseno!");
			}else{
				log.error("Parsiranje NIJE uspesno zavrseno!");
			}
			
		} 
		finally {
			if (br != null) try { br.close(); } catch (IOException e1) { log.error(e1.getMessage(), e1); }
		}

	}
	
	
}