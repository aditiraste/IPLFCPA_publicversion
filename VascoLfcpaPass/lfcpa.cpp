/*******************************************************************************************************
	              "Interprocedural LFCPA"
Author:      Aditi Raste
Created on:  8/3/2022
Description: 
	     LFCPA pass performs the following taks:
	     1. Interprocedural Strong Liveness Analysis
	     2. Interprocedural Points-to Analysis
Last Updated: 
Current Status: 
**********************************************************************************************************/

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include <bits/stdc++.h>
#include <cxxabi.h>
#include "llvm/IR/Module.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/InstrTypes.h"
//#include "TransformIR.cpp"
#include <string.h>
#include "Analysis.h"
#include "llvm/IR/Module.h"
//#include "include/TransformIR.h"


using namespace llvm;
using namespace spatial;

//using forwardDataFlowValue = std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>>;
//using backwardDataFlowValue = std::set<std::pair<Token*, std::string>>;
using F = std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>>;
using B = std::set<std::pair<Token*, std::string>>;

class IPLFCPA : public Analysis<F, B> {  //, public Transform {
	Token* dummy = IM->extractDummy("?");           /* used to set the name of dummy variable*/
	Token* dangling = IM->extractDummy("dangling"); /* local pointees of global pointers*/
public: 
	IPLFCPA();
	F getBoundaryInformationForward();
	F getInitialisationValueForward();
	B getBoundaryInformationBackward();
	B getInitialisationValueBackward();
	bool EqualDataFlowValuesBackward(const B& d1, const B& d2) const;
	bool compareToken(Token*, Token*) const;
	B performMeetBackward(const B&, const B&) const;
	B computeInFromOut(fetchLR &I);
	std::string fetchLhsIndex (fetchLR*, Token*);
	B eraseFromLin(Token*, std::string, B);
	B insertRhsLin(B, std::vector<std::pair<Token*, int >>, F, fetchLR &);
	B getPurelyGlobalComponentBackward(const B& dfv) const;
	void printDataFlowValuesBackward(const B& dfv) const;
	F computeOutFromIn(fetchLR &I);
	std::string fetchRhsIndxfrmPin(F, Token*);
        F restrictByLivness(F, B);
	B backwardMerge(B, B);
        F forwardMerge(F, F);   
	bool EqualDataFlowValuesForward(const F &d1, const F &d2) const;
	F performMeetForward(const F& d1, const F& d2) const;  
	F getPurelyGlobalComponentForward(const F& dfv) const;      
	void printDataFlowValuesForward(const F &dfv) const;
	pair<F, B> CallInflowFunction(int, Function *, BasicBlock *, const F &, const B &);
	pair<F, B> CallOutflowFunction(int, Function *, BasicBlock *, const F &, const B &, const F &, const B &);
	B getLocalComponentB(const B &);
	void printCurrPinPout(F);
	void printCurrLinLout(B);
	F getPurelyLocalComponentForward(const F& dfv) const;
};

IPLFCPA::IPLFCPA() : Analysis<F, B>(true, true){ };
IPLFCPA lfcpaObj;
bool vFlag = true;
bool flgBitcast = true;
std::set<int> insBitcastSet;


F IPLFCPA::getPurelyLocalComponentForward(const F& dfv) const {
 errs() << "\n Inside getPurelyLocalComponentForward.............";
 F fwdLocalVal;
 for (auto d : dfv) {
    std::pair<Token*, std::string> pointer = d.first;
    std::set<std::pair<Token*, std::string>> pointee = d.second;
    
    if (!pointer.first->isGlobalVar()) {
	for (auto p : pointee) {
	   if (!p.first->isGlobalVar())
	     fwdLocalVal[pointer].insert(p);
	}
    }//end if
 }//end for
 return fwdLocalVal;
}
void IPLFCPA::printCurrLinLout(B currB) {
//  #if defined(TRACE) || defined(PRINT)
  errs() << "\n Inside printCurrLinLout............";
 // #endif
  for (auto inIt : currB)  {
          errs() << "(" << inIt.first->getName() <<", "<< inIt.second <<") ";
  }//end for		
}


void IPLFCPA::printCurrPinPout(F currF) {
//  #if defined(TRACE) || defined(PRINT)
  errs() << "\n Inside printCurrPinPout............";
 // #endif
  for (auto inIt : currF)  {
        errs() <<"{ ";
        errs() << "(" << inIt.first.first->getName() <<", "<< inIt.first.second << ")->(";
        for (auto it : inIt.second)
        	errs() << "(" << it.first->getName() << ", " << it.second <<")" << " , ";
        errs() <<") }";
  }//end for		
}


B IPLFCPA::getLocalComponentB(const B & dfv) {
	errs() << "\n Inside getLocalComponentB.............";
	B LocalValues;	
	for (auto d : dfv) {
 	if (!d.first->isGlobalVar()) 
	  LocalValues.insert(d);	
	}
	return LocalValues;
}

pair<F, B> IPLFCPA::CallOutflowFunction(int current_context_label, Function * target_Function, BasicBlock *bb, const F & a3, const B & d3, const F & a1, const B & d1) {
	errs() << "\n Inside CallOutflowFunction..............";
	errs() << "\n Printing values of a1";
        printCurrPinPout(a1);
	errs() << "\n Printing values of d1";
	printCurrLinLout(d1);
	errs() << "\n Printing values of a3";
        printCurrPinPout(a3);
	errs() << "\n Printing values of d3";
	printCurrLinLout(d3);

	
	pair<F, B> retOUTflow;
	B callnodeLin = d3;
 	B LocalComponent = getLocalComponentB(d1);
	
	for (auto i : LocalComponent) 
		callnodeLin.insert(i);

	retOUTflow.first = a1;  //check once!!
	retOUTflow.second = callnodeLin; 
	return retOUTflow;
}

pair<F, B> IPLFCPA::CallInflowFunction(int current_context_label, Function * target_Function, BasicBlock *bb, const F &a1, const B &d1) {
	errs() << "\n Inside CallInflowFunction...............";
	pair<F, B> calleeInflowPair;
	B calleeLOUT;
	F calleePIN;

        printCurrPinPout(a1);
	printCurrLinLout(d1);

	errs() << "\n Checking backward values first........";

	//set the backward value 
	for (auto d : d1) {  errs() << "\n For loop 1";
		if (d.first->isGlobalVar()) {  
			errs() << "\n Bck val is global = "<< d.first->getName();
			calleeLOUT.insert(d);
		}	
	}

	errs() << "\n Checking forward values now......";
	//set the forward value
	for (auto a : a1) { errs() << "\n FOR loop F 1";
		if (a.first.first->isGlobalVar()) { errs() << "\n Ptr is global: : "<<a.first.first->getName();
		//ptr is global now check pointees
		   for (auto p : a.second){ errs() << "\n Checking Pointeess....";
			if (p.first->isGlobalVar()) {	errs() << "\n Pointee is global: "<<p.first->getName();
			    calleePIN[a.first].insert(p); }
			else 
			    calleePIN[a.first].insert(std::make_pair(dangling,"-1"));
		   }//end inner for
		}//end if	
	}//end for
	calleeInflowPair = std::make_pair(calleePIN,calleeLOUT);
	return calleeInflowPair;
}

void IPLFCPA::printDataFlowValuesForward(const F &dfv) const {
 for (auto inIt : dfv)  {
        errs() <<"{ ";
        errs() << "(" << inIt.first.first->getName() <<", "<< inIt.first.second << ")->(";
        for (auto it : inIt.second)
        	errs() << "(" << it.first->getName() << ", " << it.second <<")" << " , ";
        errs() <<") }";
  }//end for
}

//test test
F IPLFCPA::getPurelyGlobalComponentForward(const F& dfv) const {
  errs() << "\n Inside getPurelyGlobalComponentForward...........";
  F globalComponent;
  for (auto d : dfv) {
     std::pair<Token*, std::string> key = d.first;
     std::set<std::pair<Token*, std::string>> value = d.second;

     if (key.first->isGlobalVar()) {
	for (auto i : value) {
		if (i.first->isGlobalVar())
			globalComponent[key].insert(i);
		else
			globalComponent[key].insert(std::make_pair(dangling, ""));	
	}
     }
  }
  return globalComponent;
}

/* Testing the below function*****/
F IPLFCPA::performMeetForward(const F& d1, const F& d2) const {
   errs() << "\n Inside performMeetForward..............";
   F retMeetINF = d1;
  for (auto it : d2) {
        std::pair<Token*, std::string> key = it.first;
        std::set<std::pair<Token*, std::string>> value = it.second;
	std::set<std::pair<Token*, std::string>> prevValue = retMeetINF[key];
	bool flag = false;

	if (!prevValue.empty()) {
	   for (auto pv : prevValue ) {
		for (auto nv : value) {
	  	   if (!(nv.first->getName() == pv.first->getName())) 
			flag = true;
		   else if (!(nv.second == pv.second))
			flag = true;						
		}
	   }
	} 
	else {
	    #ifdef PRINT
	    errs()<< "\n Key not in prevPOUT";
	    #endif
            flag = true;        
	}
	if (flag) {
		for (auto itValues : value)
        	     retMeetINF[key].insert(itValues);
	}
     }//end for
     return retMeetINF;



}

bool IPLFCPA::EqualDataFlowValuesForward(const F &d1, const F &d2) const {
 errs() << "\n Inside EqualDataFlowValuesForward...............................";

if (d1.empty() and d2.empty())
	return true;
   else if ( (d1.empty() and !d2.empty()) or (!d1.empty() and d2.empty()))
	return false;
   else if (!d1.empty() and !d2.empty()) {
   
      for ( auto NEW : d1) { 
	std::pair<Token*, std::string> newPTR = NEW.first;
	std::set<std::pair<Token*, std::string>> newPointee = NEW.second;
	bool vdiff = true;

	for (auto PREV : d2) {
	  std::pair<Token*, std::string> prevPTR = PREV.first;
	  std::set<std::pair<Token*, std::string>> prevPointee = PREV.second;

	 if (compareToken(newPTR.first, prevPTR.first) and newPTR.second == prevPTR.second) { 
	   if (newPointee.empty() and prevPointee.empty()) 
		vdiff = false;
	   else if ((!newPointee.empty() and prevPointee.empty()) or (newPointee.empty() and !prevPointee.empty())) 
		vdiff = true;
	   else if (!newPointee.empty() and !prevPointee.empty()) { 
		for (auto np : newPointee) { 
		   vdiff = true; 
		   for (auto pp : prevPointee) {  
			if (compareToken(np.first, pp.first) and np.second == pp.second) { 
			#ifdef PRINT
			errs() << "\n Set change to false. ";	
			#endif
			vdiff = false;
		        }
		   }//inner for
		   if (vdiff) 
		     return false;
	         }//outer for
	   }//end else
	 }//end if		 
	}//end inner for
	if (vdiff) 
	  return false; 
      }//end outer for
    }//end else
    #ifdef PRINT
    errs() << "\n NO CHANGE. ";
    #endif
    return true;
}

///Merges the liveness information
B IPLFCPA::backwardMerge(B prevOUT, B succIN) {
   errs() << "\n Inside backwardMerge................";
   for (auto valueInSuccIN : succIN)         // prevOUT merge succIN
           prevOUT.insert(valueInSuccIN);
   return prevOUT;
}

///Merges points-to information
F IPLFCPA::forwardMerge(F a1, F a2) {
 errs() << "\n Inside forwardMerge.................";
     
     for (auto it : a2) {
        std::pair<Token*, std::string> key = it.first;
        std::set<std::pair<Token*, std::string>> value = it.second;
	std::set<std::pair<Token*, std::string>> prevValue = a1[key];
	bool flag = false;

	if (!prevValue.empty()) {
	   for (auto pv : prevValue ) {
		for (auto nv : value) {
	  	   if (!(nv.first->getName() == pv.first->getName())) 
			flag = true;
		   else if (!(nv.second == pv.second))
			flag = true;						
		}
	   }
	} 
	else {
	    #ifdef PRINT
	    errs()<< "\n Key not in prevPOUT";
	    #endif
            flag = true;        
	}
	if (flag) {
		for (auto itValues : value)
        	     a1[key].insert(itValues);
	}
     }//end for
     return a1;
}


///Restricts points-to information at a program point by the corresponding liveness information
F IPLFCPA::restrictByLivness(F valPointsTo, B valLiveness) {
   errs() << "\n Inside restrictByLivness().......";

	F resPointsTo;		
	for (auto lv : valLiveness) {
		for (auto pt : valPointsTo) {
		    std::pair<Token*, std::string> key = pt.first;
		    std::set<std::pair<Token*, std::string>> value = pt.second;
		    if (objArray.checkArray(lv.first,lv.second)){ 
			if (compareToken(lv.first, key.first)) 
				resPointsTo[key] = value;		 	
		    }
		    else {
			if (compareToken(lv.first, key.first) and lv.second == key.second) 
				resPointsTo[key] = value;										
		    }
		}//inner for
	}//outer for
	return resPointsTo;
}

///Returns index of RHS 
std::string IPLFCPA::fetchRhsIndxfrmPin(F Pin, Token* RHS) {
	#if defined(TRACE) || defined(PRINT)
	errs() << "\n Inside fetchRhsIndxfrmPin............... ";
	#endif
	std::string emptystring;
	for (auto i : Pin) {
		if (compareToken(RHS,i.first.first)) 
			return i.first.second;
	}
	return emptystring;
}


F IPLFCPA::computeOutFromIn(fetchLR &I) {
  errs() << "\n Inside computeOutFromIn......................";
  std::pair<Token*, int> tempLHS;
  Token* lhsVal; int indirLhs;
  std::vector<std::pair<Token*, int>> rhsVector;
  F OUTofInst, INofInst, prevNewOutofInst;
  std::pair<Token*, int > rhsVal;
  int rhsIndir;
  bool pFlag = false; /* Required to check must pointees */

  //Fetch the LHS and the RHS of instr I
   tempLHS = I.getLHS();
   lhsVal = tempLHS.first;  
   indirLhs = tempLHS.second;
   if (lhsVal != NULL and !I.getUse() and !I.getKill()) {
//	#ifdef PRINT
	errs() << "\n LHS in loop = "<<lhsVal->getName()<<" indir= "<<indirLhs;
//	#endif
   }
   rhsVector = I.getRHS();
   for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++)
   {					
	rhsVal = *r;
	rhsIndir = rhsVal.second;
//	#ifdef PRINT
	errs() << "\n Rhs in loop: <"<< rhsVal.first->getName() << ", "<<rhsVal.second <<">";		
//      #endif
   }

  //Fetch the previous OUT of the instr
  prevNewOutofInst = getForwardComponentAtOutOfThisInstruction(I);
  
  //Fetch current IN of the instr
  INofInst = getForwardComponentAtInOfThisInstruction(I);
 
  //Copy IN into OUT
  OUTofInst = INofInst; 

  bool notPINEmpty = false; //check if PIN is empty 
  bool foundPointee = false; //check if pointee of Rhs is found in PIN
 
  B backwardOUT = getBackwardComponentAtOutOfThisInstruction(I);;
  
  if (I.getPhi()) {
   #ifdef PRINT
   errs() << "\n Instr is PHI. ";
   #endif
   B rhsSet;
   std::string tempIndx;
  
   for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++) {
        rhsVal = *r;
	if (rhsVal.second == 0 and rhsVal.first->getName() != "NULL") { //..=&u
	   #ifdef PRINT
	   errs() << "\n Rhs indir is 0. ";
	   #endif			
	   if (rhsVal.first->getIsPhiGEPOpd()) {
	      #ifdef PRINT
	      errs() << "\n Rhs is a PHI GEP Operand. ";
	      #endif
	      if ((rhsVal.first->getIsArray() and rhsVal.first->isGlobalVar()) or
	           rhsVal.first->getIsAlloca() or !rhsVal.first->isValPointerType())  {
		   #ifdef PRINT
		   errs() << "\n PHI GEP operand is an array or alloca. ";
		   #endif
		   rhsSet.insert(std::make_pair(rhsVal.first,rhsVal.first->getFieldIndex()));
		   notPINEmpty = true; foundPointee = true;
	      }
	      else { 
		 #ifdef PRINT
		 errs() << "\n PHI GEP operand is not an array. ";
		 #endif
		 bool isArrFlg = false; //set if pointee in Pin is array then newToken after transfer should be an array
	         for (auto p : INofInst) { 
		      notPINEmpty = true; 
		      std::pair<Token*, std::string> Pointer = p.first;
		      std::set<std::pair<Token*, std::string>> Pointee = p.second;
		      if (compareToken(Pointer.first, rhsVal.first)) {  
			 foundPointee = true; //pointee of rhs in PIN
			               
		      for (auto s : Pointee){   
			 if (s.second == "") { 	   
			     s.first->setIndex(rhsVal.first);
			     s.second = s.first->getFieldIndex();  //set index again for Pout
			     rhsSet.insert(s);						
			     if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex()))
					objArray.setArray(s.first, s.second);
			 }//endif
			 else {
			    #ifdef PRINT
			    errs() << "\n Nested structures in source code. ";
			    #endif
			    /*Check if pointee in Pin is an array*/
			    if (objArray.checkArray(s.first,s.second)) {
			      #ifdef PRINT
			      errs() << "\n Pointee in Pin is an array. "; //new token should be included in the array map
			      #endif
			      isArrFlg = true;
			    }
			    Token *newToken = new Token(s.first);
			    newToken->setIndex(rhsVal.first, s.second);
			    rhsSet.insert(std::make_pair(newToken,newToken->getFieldIndex()));
			    if (isArrFlg)		
				objArray.setArray(newToken,newToken->getFieldIndex());
			    else {
				if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex())) 
				   objArray.setArray(newToken,newToken->getFieldIndex());
			    }
			 }//else nested
			}//for pointee
		       }//if compare
		 }//for InofInst
                }//else GEP not array		      		   		
	       }//end if phiGEPOpd
	       else {
		    #ifdef PRINT
		    errs() << "\n Non-GEP PHI operand. ";
		    #endif
		    rhsSet.insert(std::make_pair(rhsVal.first, ""));
		    notPINEmpty = true; foundPointee = true;
	       }
	       if (notPINEmpty) {
		   if (foundPointee)
			OUTofInst[std::make_pair(tempLHS.first, "")] = rhsSet;
		   }
        }//end if rhsindir=0
	else if (rhsVal.second == 1) { // ..=y. Find pointees from Pin
	    #ifdef PRINT
	    errs() << "\n Rhs Indir is 1. ";
	    #endif
	    std::queue<Token*> q;
	    std::queue<std::string> q1;
	    q.push(rhsVal.first); 			

            while (rhsVal.second == 1 and !q.empty())     {
        	Token* rhsTemp = q.front();
        	q.pop();			    	
		tempIndx = fetchRhsIndxfrmPin(INofInst, rhsTemp);
		#ifdef PRINT
		errs()<<"\n Fetch pointees of t1 from Pin. ";
		#endif

		for (auto IN : INofInst) {
			notPINEmpty = true; 
			if (compareToken(rhsTemp, IN.first.first) and tempIndx == IN.first.second) {
			    #ifdef PRINT
			    errs() << "\n Pointees of Rhs found in Pin. ";
			    #endif
			    std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
		  	    for (auto pointee : pointeeSet) {
			    	q.push(pointee.first);
			    	q1.push(pointee.second);
				foundPointee = true;
		 	    }//end for
		    	 }//end if
		}//end outer for	       	            		    	
		rhsVal.second--;
           }//end while
	   /* Loop to fetch pointees of RHS */
    	   while (!q.empty())      {
       	      Token* rhsValue = q.front();
	      std::string IndexRhs = q1.front();
       	      q.pop();   q1.pop();
       	      rhsSet.insert(std::make_pair(rhsValue, IndexRhs));				    
	   }
	}//end else
       }//end for
	if (notPINEmpty) {
	   if (foundPointee)
	      	   OUTofInst[std::make_pair(lhsVal, lhsVal->getFieldIndex())] = rhsSet; 
         }
      }//end if phi
      else if (I.getUse())	{
//	#ifdef PRINT
	errs() <<"\n Instr is a USE. ";
//	#endif
	std::set<std::pair<Token*, std::string>> rhsSet;
	std::string tempIndx;
	std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>> newOutofInst;

        for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++) {
	  rhsVal = *r; 
	  if (rhsVal.first->getIsIcmpGEPOpd()) {
	    #ifdef PRINT
	    errs() <<"\n USE operand is a GEP. ";
	    #endif

	   if ((rhsVal.first->getIsArray() and rhsVal.first->isGlobalVar()) or
		rhsVal.first->getIsAlloca() or !rhsVal.first->isValPointerType())  {
		#ifdef PRINT
		errs() << "\n USE Inst: GEP operand is an array or alloca";
 		#endif
		rhsSet.insert(std::make_pair(rhsVal.first,rhsVal.first->getFieldIndex()));
	   	notPINEmpty = true; foundPointee = true;
	   }//end if
	   else { 
		#ifdef PRINT
		errs() << "\n USE Inst: GEP operand is not an array. ";
 		#endif
	        bool isArrFlg = false; 
	        for (auto p : INofInst) { 
		    notPINEmpty = true; 
		    std::pair<Token*, std::string> Pointer = p.first;
		    std::set<std::pair<Token*, std::string>> Pointee = p.second;
		    if (compareToken(Pointer.first, rhsVal.first)) {  
		 	 foundPointee = true; //pointee of rhs in PIN
			 for (auto s : Pointee){   
			    if (s.second == "") { 	   
				s.first->setIndex(rhsVal.first);
				s.second = s.first->getFieldIndex();  //set index again for Pout
				rhsSet.insert(s);						
				if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex()))
					objArray.setArray(s.first, s.second);
			    }
			    else {
				#ifdef PRINT
				errs() << "\n Nested structures in source code. ";
				#endif
				/*Check if pointee in Pin is an array*/
				if (objArray.checkArray(s.first,s.second)) {
			  	   #ifdef PRINT
				   errs() << "\n Pointee in Pin is an array."; 
			   	   #endif
				   isArrFlg = true;
				}
				Token *newToken = new Token(s.first);
				newToken->setIndex(rhsVal.first, s.second);
				rhsSet.insert(std::make_pair(newToken,newToken->getFieldIndex()));
			
				if (isArrFlg)		
				  objArray.setArray(newToken,newToken->getFieldIndex());
				else {
				  if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex())) 
				    objArray.setArray(newToken,newToken->getFieldIndex());
		                }
			    }//else
			 }//for			
		    }//if		      		   		
		  }//end for
		}//end else not array       			
		if (notPINEmpty) {
		   if (foundPointee)
			OUTofInst[std::make_pair(tempLHS.first, "")] = rhsSet;
		}
		//######OUTPTA[std::make_tuple(contextId,B,instrCount)] = OUTofInst; 
		newOutofInst = restrictByLivness(OUTofInst, backwardOUT);
        }//end outermost if
        else {
 	  #ifdef PRINT
	  errs() << "\n USE Inst: Normal operand. ";
 	  #endif
	  /* Just restrict Pout by Lout */
	  //#####OUTPTA[std::make_tuple(contextId,B,instrCount)] = OUTofInst; 
	  newOutofInst = restrictByLivness(OUTofInst, backwardOUT);
	}
      }//end for
      errs() << "\n Printing forward values: ";
      printDataFlowValuesForward(newOutofInst);
      errs() << "\n ----------------------------------";
      return newOutofInst;		
      }//end if USE
      else if (I.getKill()) {
	#ifdef PRINT
	errs() << "\n Instr is a Kill. ";
	#endif
      }
      else if (I.getBitcast()) {
         //#ifdef PRINT
	 errs() << "\n Instr is a Bitcast. ";
	 //#endif
	 flgBitcast = true;
	 std::set<std::pair<Token*, std::string>> rhsSet; 
	 Token* rhsValue = rhsVal.first;
	 int rhsInTmp = rhsIndir;
	 std::string tempIndx;
	
 	 if (rhsIndir == 1)  {
	   #ifdef PRINT
	   errs() << "\n Rhs Indir is 1. ";
	   #endif
	   std::queue<Token*> q;
	   std::queue<std::string> q1;
	   q.push(rhsValue);			
           while (rhsInTmp == 1 and !q.empty())     {
                Token* rhsTemp = q.front();
                q.pop();

	        if (rhsTemp->getIsAlloca()) {
		   q.push(rhsTemp); 	
		   rhsTemp->resetIndexToZero();
		   q1.push(rhsTemp->getFieldIndex());
		   rhsTemp->setIsOpBitcast();
		}
		else if (rhsTemp->isValPointerType()) {  
        	   tempIndx = fetchRhsIndxfrmPin(INofInst, rhsTemp);
		   #ifdef PRINT
		   errs() << "\n Fetch pointees of t1 from Pin. ";
		   #endif
		   for (auto IN : INofInst) {
		     notPINEmpty = true;
		     if (compareToken(rhsTemp, IN.first.first) and tempIndx == IN.first.second) {
		        foundPointee = true;
			#ifdef PRINT
			errs() << "\n Pointees of Rhs found in Pin. ";
			#endif
			std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
			for (auto pointees : pointeeSet) {
			    if (pointees.second == "") { 
				q.push(pointees.first); 	
			        pointees.first->resetIndexToZero();
			        q1.push(pointees.first->getFieldIndex());
				pointees.first->setIsOpBitcast();
			    }
			    else { 
				#ifdef PRINT
				errs()<< "\n Nested Union in source program. ";
				#endif
				Token *newToken = new Token(pointees.first);
				newToken->resetIndexToZero(newToken->getFieldIndex());
				q.push(newToken);
				q1.push(newToken->getFieldIndex());
				newToken->setIsOpBitcast();
			    }//end else nested
	 	        }//end for
		      }//end if
                    }//end outer for	       	            		    	
               }//end if 
	       else {
		#ifdef PRINT
		errs() << "\n *****Reached the third condition "; //check if this condition is ever satisfied
		#endif
	       }					
	       rhsInTmp--;
           }//end while
	   while (!q.empty())      {
	    Token* rhsValue = q.front();
	    std::string IndexRhs = q1.front();
	    q.pop();   q1.pop();
	    rhsSet.insert(std::make_pair(rhsValue, IndexRhs));				    
	  }
	}//end else if=1
	if (notPINEmpty) { /* necessary condition to avoid i23->() in POUT */
		if (foundPointee) 
	 	  OUTofInst[std::make_pair(lhsVal, lhsVal->getFieldIndex())] = rhsSet;						
	}
      }//end if Bitcast
      else if (I.getGEP()) {
	//#ifdef PRINT
	errs() << "\n Instr is a GEP x = gep y[indx]. ";
	//#endif
	std::set<std::pair<Token*, std::string>> rhsSet;   
	std::string tempIndx; 
	std::string rhsIndx;
	
        /*Check if gep operand is an array or alloca ptr*/
	/* If GEP operand is not a pointer the instr should behave as a normal x=&y instr*/
	if (rhsVal.first->getName() != "NULL") {
	  if (rhsVal.first->getIsOneGEPIndx()) {
	    #ifdef PRINT
	    errs() << "\n GEP has single index. No transfer of links required.";
	    #endif		
	    for (auto p : INofInst) { 
	        notPINEmpty = true; //Pin is non-empty
		std::pair<Token*, std::string> Pointer = p.first;
		std::set<std::pair<Token*, std::string>> Pointee = p.second;
		if (compareToken(Pointer.first, rhsVal.first)) {  
		 foundPointee = true; //pointee of rhs in PIN
		 for (auto s : Pointee)
		    rhsSet.insert((s));
		} //end if
	     }//end outer for  
  	    }//end if OneGepIndx
  	    else if ((rhsVal.first->getIsArray() and rhsVal.first->isGlobalVar()) or rhsVal.first->getIsAlloca()) {
		#ifdef PRINT
		errs() << "\n GEP operand is an global array/alloca. Instr is normal x=&y. ";
		#endif
		rhsSet.insert(std::make_pair(rhsVal.first,rhsVal.first->getFieldIndex()));
		notPINEmpty = true; foundPointee = true;
	    }
	    else if (rhsVal.first->isValPointerType())  { 
	      #ifdef PRINT
	      errs() << "\n GEP operand is a pointer. ";
	      #endif
	      bool isArrFlg = false; //set if pointee in Pin is an array then the newToken after transfer should also be an array

       	      for (auto p : INofInst) { 
	        notPINEmpty = true; //Pin is non-empty
	        std::pair<Token*, std::string> Pointer = p.first;
	        std::set<std::pair<Token*, std::string>> Pointee = p.second;
	        if (compareToken(Pointer.first, rhsVal.first)) {  
		 foundPointee = true; //pointee of rhs in PIN
		 for (auto s : Pointee){   
		    /* If Pointee is an array then no transfer of links and ignore indices*/
		    if (s.first->getIsArray()) {
		       #ifdef PRINT
	   	       errs()<<"\n GEP operand pointee is an array. Ignore indices.";
	               #endif		
		       rhsSet.insert(s);
		       objArray.setArray(s.first, s.second);
		    }
		    else if (s.second == "") { 	   
			s.first->setIndex(rhsVal.first);
			s.second = s.first->getFieldIndex();  //set index again for Pout
			rhsSet.insert(s);						
			if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex()))
				objArray.setArray(s.first, s.second);
		    }
		    else {
			#ifdef PRINT
			errs() << "\n Nested structures in source code. ";
			#endif
			/*Check if pointee in Pin is an array*/
			if (objArray.checkArray(s.first,s.second)) {
			   #ifdef PRINT
			   errs() << "\n Pointee in Pin is an array. "; //new token should also be included in the array map
			   #endif
			   isArrFlg = true;
			}
			Token *newToken = new Token(s.first);
			newToken->setIndex(rhsVal.first, s.second);
			rhsSet.insert(std::make_pair(newToken,newToken->getFieldIndex()));
			
			if (isArrFlg)		
				objArray.setArray(newToken,newToken->getFieldIndex());
			else {
				if (objArray.checkArray(rhsVal.first,rhsVal.first->getFieldIndex())) 
					objArray.setArray(newToken,newToken->getFieldIndex());
			}
		     }//else
		 }//for			
	      }//if		      		   		
	  }//end for
        }//end if pointer
	else {
	   #ifdef PRINT
	   errs() << "\n GEP operand is not a pointer";
	   #endif
	   rhsSet.insert(std::make_pair(rhsVal.first,rhsVal.first->getFieldIndex()));		  
	}//not a pointer

	if (notPINEmpty) {
	  if (foundPointee)
	    OUTofInst[std::make_pair(tempLHS.first, "")] = rhsSet;			
	}
      }//end if not null		
   }//end gep
   else if (I.getCall()) {
	errs() << "\n Instructioon is a call....";	

   }
   else	{
	 //#ifdef PRINT
	 errs() << "\n Normal instruction. ";	
	 //#endif
	 long long int counter = 0;
	 std::set<std::pair<Token*, std::string>> rhsSet; 
	 Token* rhsValue = rhsVal.first;
	 int rhsInTmp = rhsIndir;
	 std::string tempIndx; 

	 /* First get points-to pairs from Rhs */
 	 /* case 1: x=&u */
	 if (rhsIndir == 0) {	
		//#ifdef PRINT
		errs() << "\n Rhs indir = 0 ";
		//#endif
		foundPointee = true;
		notPINEmpty = true;
		 if (I.getGOPRhs()) { 
			errs() << "\n Instr is GOPRhs.............";
			//rhsSet.insert(std::make_pair(rhsValue, objStruct.getStructFieldIndxRhs(instrCount))); *working on it*
		 }
		 else if (I.getGEP()) {
			//#ifdef PRINT
			errs() << "\n Inst is a GEP. ";
			//#endif
			rhsSet.insert(std::make_pair(rhsValue, rhsValue->getFieldIndex()));
		 }
		 else {
		  	#ifdef PRINT
			errs() << "\n Normal instruction. ";
		  	#endif
		        if (I.getBitcastRhs()) 
			   rhsSet.insert(std::make_pair(rhsValue, rhsValue->getFieldIndex()));
			else 
			   rhsSet.insert(std::make_pair(rhsValue, ""));  
		}
	 }//end if
	 else if (rhsIndir == 1) /* case 2: x=t1 or t1=x or *t2=t1 */ {
		//#ifdef PRINT
		errs() << "\n case 2: x=t1 or t1=x or *t2=t1 ";
		//#endif
		std::queue<Token*> q;
		std::queue<std::string> q1;
		foundPointee = false;
	        q.push(rhsValue); 	
			
                while (rhsInTmp == 1 and !q.empty())     {
                    Token* rhsTemp = q.front();
                    q.pop();
		    if (rhsTemp->isValPointerType()) {  
                   	tempIndx = fetchRhsIndxfrmPin(INofInst, rhsTemp);
			//#ifdef PRINT
			errs()<<"\n Fetch pointees of t1 from Pin. ";
			//#endif
			if (objArray.checkArray(rhsTemp, tempIndx)) {
				for (auto IN : INofInst) {
					notPINEmpty = true;
			    		if (compareToken(rhsTemp, IN.first.first)) {
						//#ifdef PRINT
						errs() << "\n Pointees of Rhs found in Pin. ";	
						//#endif
						std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
					  	for (auto pointee : pointeeSet) {
		       				      q.push(pointee.first);
						      q1.push(pointee.second);
			 			}//end for
			    		}//end if
		        	}//end outer for
			}
			else {
				for (auto IN : INofInst) {
				 notPINEmpty = true;
			    	 if (compareToken(rhsTemp, IN.first.first) and tempIndx == IN.first.second) {
					//#ifdef PRINT
					errs() << "\n Pointees of Rhs found in Pin. ";
					//#endif
					std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
			  		for (auto pointee : pointeeSet) {
		       		      		q.push(pointee.first);
				      		q1.push(pointee.second);
			 		}//end for
			    	}//end if
		               }//end outer for
			}//end else	       	            		    	
		    }//end if 
		    rhsInTmp--;
        	}//end while
		/* Loop to fetch pointees of RHS */
	        while (!q.empty())      {
		    Token* rhsValue = q.front();
		    std::string IndexRhs = q1.front();
		    q.pop();    q1.pop();
		    rhsSet.insert(std::make_pair(rhsValue, IndexRhs));
		    foundPointee = true;				    
                }	
	}//end else if=1
	else if (rhsIndir == 2) { /* case 3: x=*t or t1=*t2 */
		//#ifdef PRINT
		errs() << "\n Case 3: x=*t1 or t1=*t2 ";
		//#endif
		Token* marker = IM->extractDummy("mark");
		std::string empty = "";
		std::queue<Token*> q;
		std::queue<std::string> q1;
			
	        if (!INofInst.empty()) { 
		 q.push(rhsValue);
		 q.push(marker);
		 tempIndx = fetchRhsIndxfrmPin(INofInst, rhsValue);
		 q1.push(tempIndx); q1.push(empty);

		 while (rhsInTmp > 0 and !q.empty())  { 
       		     Token* rhsTemp = q.front(); q.pop(); 
		     std::string tempIndx = q1.front();  q1.pop();
		     //if (rhsTemp->getName() != "NULL") {
		     if (rhsTemp->getName() != "mark") {  			
		      for (auto IN : INofInst) {  
			notPINEmpty = true;
			  if (rhsTemp->getIsArray()) {
			     #ifdef PRINT
			     errs()<<"\n Rhs is an array so ignoring the indices. ";
			     #endif 
			     if (compareToken(rhsTemp, IN.first.first)) {
				#ifdef PRINT
				errs() << "\n Array: Pointees of Rhs found in Pin. ";
				#endif
			        std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
			  	for (auto pointee : pointeeSet) {
			      		q.push(pointee.first);
			      		q1.push(pointee.second);
				}//end for	
				q.push(marker);q1.push(empty);
			    }//end inner if
			}//end outer if
			else { 
				if (compareToken(rhsTemp, IN.first.first) and tempIndx == IN.first.second) {
				#ifdef PRINT
				errs() << "\n Pointees of Rhs found in Pin. ";
				#endif
			        std::set<std::pair<Token*, std::string>> pointeeSet = IN.second;
			        for (auto pointee : pointeeSet) { 
			     		q.push(pointee.first);
			      		q1.push(pointee.second);
		 	  	}//end for
				q.push(marker);q1.push(empty);
			     }//end if
			}//end else not array
		      }//end outer for	       	            		    	
		  }//end if not Null token
		  else
		    rhsInTmp--;  
	        }//end while
	    }//end if PIN not empty
	   /* Loop to fetch pointees of RHS */
  		while (!q.empty() and !q1.empty()) {
		    #ifdef PRINT
	       	    errs() << "\n Fetching pointees of RHS. ";
		    #endif
        	    Token* rhsValue = q.front();
		    std::string rhsIndx = q1.front();	
	 	    q.pop();	    q1.pop();
		    if (rhsValue->getName() != "mark") {
       			    rhsSet.insert(std::make_pair(rhsValue,rhsIndx));
	    	    	    foundPointee = true; //only if x=*t2 P(P(t2)) are found in PIN 
		    }
       	         }
 	}//end else if=2

	/* Fetch the pointees of Lhs */
	std::queue<Token*> q1;	    
        q1.push(lhsVal); 
                
	/* Check if Lhs is an Array Type */
	if (indirLhs == 1 and tempLHS.first->getIsArray()) {		
	 //#ifdef PRINT
	 errs() << "\n Lhs is an array. No kill.";
	 //#endif
	 Token* lhsTemp = q1.front();
       	 q1.pop();
	 bool flgPointee = false;
	 std::string ind = fetchRhsIndxfrmPin(INofInst, lhsTemp);
	 for (auto p : INofInst) {
	     std::pair<Token*, std::string> Pointer = p.first;
	     std::set<std::pair<Token*, std::string>> Pointee = p.second;			
	     if (compareToken(Pointer.first, lhsTemp) and Pointer.second == ind) {
	     #ifdef PRINT
	     errs() << "\n Pointer found in Pin. ";
	     #endif				
	     for (auto s : Pointee){
		if (s.first->getName() != "?") { 
		   flgPointee = true;
		   rhsSet.insert(std::make_pair(s.first, s.second));
		}//if
	     }//for			
	    }//if
          }//end for			
	  if (notPINEmpty) {
	    if (foundPointee)
		 OUTofInst[std::make_pair(lhsTemp, lhsTemp->getFieldIndex())] = rhsSet;							
	   }
         }//end if	

 	while (indirLhs>1 and !q1.empty() and (!I.getGEP())) {  
               	Token* lhsTemp = q1.front();
               	q1.pop();
               	if (lhsTemp->isBasePointerType()) { 
		    std::string ind = fetchRhsIndxfrmPin(INofInst, lhsTemp);

		    for (auto p : INofInst) {
			notPINEmpty = true;
			std::pair<Token*, std::string> Pointer = p.first;
			std::set<std::pair<Token*, std::string>> Pointee = p.second;
			
			if (compareToken(Pointer.first, lhsTemp) and Pointer.second == ind) {
				#ifdef PRINT
				errs() << "\n Pointer found in Pin. ";
				#endif
				for (auto s : Pointee){
					s.first->setIndex(s.first);						
					q1.push(s.first);							
				}			
			}				
		      }//end for
                    }//end if
		    indirLhs--;
          }//end while
		
	  while (!q1.empty())     	{  
		counter++; /* checks for must points-to relation */
		std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>> prevPOUT = OUTofInst ;
               	Token* pointeeValue = q1.front();
		q1.pop();

	       	if (pointeeValue->getName() != "dummy") {
		      if (pointeeValue->getIsArray()) {
				std::set<std::pair<Token*, std::string>> prevRhsSet;
				#ifdef PRINT
				errs() << "\n Lhs Pointee is an array. ";
				#endif
				prevRhsSet = INofInst[std::make_pair(pointeeValue, pointeeValue->getFieldIndex())]; 
				rhsSet = backwardMerge(rhsSet,prevRhsSet);					
		      }
		      if (foundPointee)
                	         OUTofInst[std::make_pair(pointeeValue, pointeeValue->getFieldIndex())] = rhsSet; 
		}
	}//end while

	if (counter == 1) {
	   #ifdef PRINT
	   errs() <<"\n Must points-to relation. Delete points-to pairs from OutofInst \n";
	   #endif
	   pFlag = true;
	}
     }//end if normal

     F newOutofInst;
     //######OUTPTA[std::make_tuple(contextId,B,instrCount)] = OUTofInst; 
     newOutofInst = restrictByLivness(OUTofInst, backwardOUT);
	
      //printCurrPinPout(newOutofInst);
     F tempMergeOutofInst;
     std::set<Token*> emptyset;
     tempMergeOutofInst = forwardMerge(prevNewOutofInst, newOutofInst); /* merge new and previous POUT values */
     newOutofInst = tempMergeOutofInst;  /* set the value of variable newOutofInst */
     errs() << "\n Printing forward values: ";
     printDataFlowValuesForward(newOutofInst);
     errs() << "\n ----------------------------------";
     return newOutofInst;     
}

void IPLFCPA::printDataFlowValuesBackward(const B& dfv) const {
  
	errs() << "{ ";
	for (auto val : dfv) 
		errs() << val.first->getName() << ", " ;
	errs() << " }";
}

B IPLFCPA::getPurelyGlobalComponentBackward(const B& dfv) const {
   errs() << "\n Inside getPurelyGlobalComponentBackward...............";
   B global_component;
   if (!dfv.empty()) {
	for (auto v : dfv) {
		if (v.first->isGlobalVar())
			global_component.insert(v);
	}//end for
   }
   return global_component;
}
///Returns index of LHS 
std::string IPLFCPA::fetchLhsIndex(fetchLR* ins, Token* LHS) {
    errs() << "\n Inside fetchLhsIndex............. ";
    std::string lhsIndx;
    if (ins->getGOPLhs() and LHS->isGlobalVar())
	return LHS->getFieldIndex();
    return  lhsIndx;
}

B IPLFCPA::computeInFromOut(fetchLR &I) {
  errs() << "\n Inside computeInFromOut...................";
  bool flagLhsLive = false;
  std::pair<Token*, int> tempLHS;
  Token* lhsVal; int indirLhs;
  std::vector<std::pair<Token*, int>> rhsVector;
  std::set<std::pair<Token*, std::string>> OUTofInst, INofInst, INofInstPrev;
  std::string indxLHS;

  //Fetch the currLOUT of instr I
  OUTofInst = getBackwardComponentAtOutOfThisInstruction(I);

  //Fetch the currPIN of instr I
  std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>> forwardIN = getForwardComponentAtInOfThisInstruction(I);

  //Copy LOUT into LIN
  for (auto outContents : OUTofInst)  	
        INofInst.insert(outContents);

  //Fetch the LHS and the RHS of instr I
   tempLHS = I.getLHS();
   lhsVal = tempLHS.first;  
   indirLhs = tempLHS.second;
   if (lhsVal != NULL and !I.getUse() and !I.getKill()) 
	   errs() << "\n Fetched LHS: "<<lhsVal->getName()<< " lhs indir: "<<indirLhs;
   rhsVector = I.getRHS();
   for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++) {					
	std::pair<Token*, int > rhsVal = *r;
	errs() << "\n Rhs in loop: <"<< rhsVal.first->getName() << ", "<<rhsVal.second <<">";
   }

   indxLHS = fetchLhsIndex(&I,lhsVal);
   	
   if (I.getUse())   {
	errs() << "\n Instr is a USE. ";	
	if (indirLhs == 99) {
	 errs() << "\n Instr is a return stmt. ";
	 std::pair<Token*, int> rhsVal = rhsVector[0];
	 INofInst.insert(std::make_pair(rhsVal.first, rhsVal.first->getFieldIndex()));
	 return INofInst;
	}//end if return
	else  {
	  errs() << "\n Instr is a comparison stmt. ";
	  for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++) {	 			
 	 	 std::pair<Token*, int > rhsVal = *r;
		if (rhsVal.first->getIsArray())
			INofInst.insert(std::make_pair(rhsVal.first, rhsVal.first->getFieldIndex()));
		else if (rhsVal.first->isValPointerType())      	      	
			INofInst.insert(std::make_pair(rhsVal.first, ""));
	 }
	 return INofInst;
	}//end else compare	
   }//end if use
   else if (I.getKill()) {
	errs() << "\n Instr is a Kill. ";
	std::pair<Token*, std::string> lhsValueMatched;
	for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++) {	 			
 	 	 std::pair<Token*, int > rhsVal = *r;
    		 indxLHS = rhsVal.first->getFieldIndex(); 
	  	 for (auto out : OUTofInst) { 
		    if (compareToken(out.first, rhsVal.first) and out.second == indxLHS) {
			lhsValueMatched = std::make_pair(out.first, out.second);
			#ifdef PRINT
	 	        errs() << "\n LHS is live on exit. ";
			#endif
	                INofInst.erase(INofInst.find(lhsValueMatched));	/* Erase LHS from LIN since it is defined here */
		    }//end if
		 }//end inner for	
	 }//end outer for
	 return INofInst;	
   }//end if kill
   else if (I.getPhi()) {
	#ifdef PRINT
	errs() << "\n Instr is a PHI instr. ";
	#endif
        std::pair<Token*, std::string> lhsValueMatched;
	/* Lhs of Phi may have indices in Lout. These indices should not be used for comparison.
	*  For ex--
	*  %i67 = phi %struct.arc* [ %i48, %bb64 ], [ %i153, %bb76 ]
	*  %i92 = getelementptr inbounds %struct.arc, %struct.arc* %i67, i64 0, i32 1
	*  %i97 = getelementptr inbounds %struct.arc, %struct.arc* %i67, i64 0, i32 7
	*/
	/* Check if Lhs is live then generate liveness of Rhs1 and Rhs2 */
	bool lvFlag = false;
	for (auto out : OUTofInst) { 
	    indxLHS = tempLHS.first->getFieldIndex(); 
	    if (compareToken(out.first, tempLHS.first)) { 
		lhsValueMatched = std::make_pair(out.first, indxLHS);
		lvFlag = true;
		#ifdef PRINT
	 	errs() << "\n LHS is live on exit. ";
		#endif
		
		auto pos = INofInst.find(lhsValueMatched); 
		if (pos != INofInst.end()) 
		        INofInst.erase(INofInst.find(lhsValueMatched));	/* Erase LHS from LIN since it is defined here */

		//If Lhs is a temporary then remove it along with its indices from LIN
		if (!tempLHS.first->isGlobalVar()) {
			auto pos = INofInst.find(std::make_pair(out.first, out.second)); 
			if (pos != INofInst.end()) 
				INofInst.erase(INofInst.find(std::make_pair(out.first, out.second)));
		}
	   }//end if
	}//end for
	
	if (lvFlag) { 
		#ifdef PRINT
		errs() << "\n Lhs is live. Hence generate liveness of Rhs. ";
		#endif

		for (std::vector<std::pair<Token*, int>>::iterator r = rhsVector.begin(); r!=rhsVector.end(); r++)	 			{					
			std::pair<Token*, int > rhsVal = *r;

			if (rhsVal.first->getIsPhiGEPOpd() and rhsVal.first->isValPointerType()) {
			   if (rhsVal.first->getIsArray())
				INofInst.insert(std::make_pair(rhsVal.first, rhsVal.first->getFieldIndex()));
			   else
				INofInst.insert(std::make_pair(rhsVal.first, ""));
		        }
			else if (rhsVal.second != 0)  
			   INofInst.insert(std::make_pair(rhsVal.first, "")); //add rhs to Lin if not ..=&u			
		}//end for
	}//end if		
   }//end phi
   else    {
    #ifdef PRINT
    errs() << "\n Computing LIN for a normal instruction. ";
    #endif
	
    bool cmpFlg = false;
    std::pair<Token*, std::string> lhsValueMatched;
    if (indirLhs == 1) { /* lhs: x=... or tmp=... */
	#ifdef PRINT	
	errs() << "\n LHS indir is 1. ";
	#endif
        //if lhs is an array then dont consider the field index. 
        if (tempLHS.first->getIsArray()) {
	   #ifdef PRINT
	   errs() << "\n LHS is an array or Inst is a GEP. Ignore field index. ";
	   #endif
	   for (auto out : OUTofInst) { 
	    if (compareToken(out.first, tempLHS.first)) { 
		lhsValueMatched = std::make_pair(out.first, "");
		flagLhsLive = true;  ///set the flag
		break;
	    }
	   }
        }//end if array
        else if (!tempLHS.first->isGlobalVar()) {//if lhs is a temporary probably gep with indices then ignore indices
	   #ifdef PRINT
	   errs() << "\n LHS is a temporary probably GEP with indices. Ignore field index but kill liveness of lhs. ";
	   #endif
	   for (auto out : OUTofInst) { 
	    if (compareToken(out.first, tempLHS.first)) { 
		#ifdef PRINT
		errs() << "\n Lhs is found in LOUT. ";
		#endif
		lhsValueMatched = std::make_pair(out.first, out.second);
		cmpFlg = true;  ///set the flag
		break;
	     }
	   }
          if (cmpFlg) {       /* Erase LHS from LIN since it is defined here */
	      #ifdef PRINT
	      errs() << "\n LHS is live on exit. Erasing Lhs from Lin. ";
	      #endif
	      INofInst = eraseFromLin(lhsValueMatched.first, lhsValueMatched.second,INofInst);
   	      flagLhsLive = true;  ///set the flag
          }
        }
        else {	//Lhs is not an array. Or Global with indices from GEP instr then consider the indices.
	   #ifdef PRINT
	   errs() << "\n LHS not an array. ";
	   #endif
	   for (auto out : OUTofInst) {
	      indxLHS = tempLHS.first->getFieldIndex(); 
	      if (compareToken(out.first, tempLHS.first) and out.second == indxLHS) {  
		#ifdef PRINT
		errs() << "\n Lhs is found in LOUT. ";
		#endif
		lhsValueMatched = std::make_pair(out.first, out.second);
		cmpFlg = true;
		break;
	      }
	   }
           /* Erase LHS from LIN since it is defined here */
          if (cmpFlg) {
	      #ifdef PRINT
	      errs() << "\n LHS is live on exit. ";
	      #endif
             //Lhs is an array but temporary or Lhs is not an array should be erased from lin
      	     if (!lhsValueMatched.first->getIsArray() or !lhsValueMatched.first->isGlobalVar() ) {
		#ifdef PRINT
		errs() << "\n LHS not an array hence erase from Lin. ";
		#endif
   		INofInst.erase(INofInst.find(lhsValueMatched));
   		flagLhsLive = true;  ///set the flag
              }
          }
      }//end inner else
   }//end if inlhs=1
   else if (indirLhs == 2) { /* lhs: *tmp=... */
	#ifdef PRINT
	errs() << "\n LHS is (temp, 2) ";
	#endif
	/* Insert LHS into Lin and RHS in Lin if pointee of LHS is in Lout */
	std::queue<Token*> q;
	std::queue<std::string> q1;
        q.push(lhsVal);
        while (indirLhs > 1 and !q.empty())   {
            Token* lhsTemp = q.front();
            q.pop();
	    bool chkFlag = false;
	    for (auto fIN : forwardIN) { 
		if (compareToken(fIN.first.first, lhsTemp)) {
			#ifdef PRINT
			errs() << "\n Pointees of LHS present in PIN. ";
			#endif
			INofInst.insert(std::make_pair(lhsTemp,indxLHS));
			std::set<std::pair<Token*, std::string>> pointees = fIN.second;
                        for (auto point : pointees)  {
			   q.push(point.first);
			   q1.push(point.second);
			}
			chkFlag = true;
		 }
	   }
           indirLhs--;
	   if (!chkFlag)   {
		#ifdef PRINT
		errs() << "\n No pointees of LHS found in PIN. ";
		#endif
		std::set<std::pair<Token*, std::string>>  INofInst; //Block propagation of liveness info
	        INofInst.insert(std::make_pair(lhsTemp,indxLHS));
		return INofInst;				
	   }          
	}//end while

	INofInstPrev = INofInst; /* maintain a backup of LIN of instr */ 
	bool flgFound = false;
  	while (!q.empty() and !q1.empty())     {
          Token* lhsPointee = q.front();
	  q.pop();
          //live and must pointer
	  #ifdef PRINT
	  errs() << "\n Check live and must pointer. ";
	  #endif
	  std::string indxPointee = q1.front();
	  q1.pop();

	  /*Check if lhsPointee is an array first*/
	  if (objArray.checkArray(lhsPointee,indxPointee)) {
		#ifdef PRINT
		errs()<< "\n Lhs Pointee is an array. ";
		#endif
  		for (auto bOUT : OUTofInst) {
		     if (compareToken(bOUT.first, lhsPointee))/*ignore indices for array*/ { 
			  #ifdef PRINT
			  errs() << "\n Pointee live at LOUT.............\n";
			  #endif
			  flagLhsLive = true;  //set the flag
			  flgFound = true;  
		     }
		}//end for	  
	  }
	  else {
		#ifdef PRINT
		errs()<<"\n Lhs Pointee not an array. ";
		#endif 
	  	for (auto bOUT : OUTofInst) {
			if (compareToken(bOUT.first, lhsPointee) and bOUT.second == indxPointee) { 
			  #ifdef PRINT
			  errs() << "\n Pointee live at LOUT.............\n";
			  #endif
			  INofInst = eraseFromLin(lhsPointee, indxPointee, INofInst);
			  flagLhsLive = true;  //set the flag
			  flgFound = true;  
		        }
	       }//end for
	 }//end else
	  if (!flgFound)	{
	     INofInst = INofInstPrev;	
	     flagLhsLive = false; 
	  }          
	}//end while
   }//end if inlhs=2

   if (flagLhsLive) { /* Insert Rhs into Lin */
	#ifdef PRINT
	errs() << "\n LHS is Live so insert RHS into LIN.  ";
	#endif
	INofInst = insertRhsLin(INofInst, rhsVector, forwardIN, I);
   }//end if flag   
  }//end normal else

  return INofInst;   
}

///Erases liveness information from IN
B IPLFCPA::eraseFromLin(Token* pointee, std::string index, B INofInst) {
  #if defined(TRACE) || defined(PRINT)
  errs() << "\n Inside function eraseFromLin..........";
  #endif 
  B newINofInst;

  if (!pointee->isGlobalVar() and !pointee->getIsAlloca()) { 
	for (auto in : INofInst) { 
		if (!(compareToken(in.first,pointee))) 
			newINofInst.insert(std::make_pair(in.first, in.second));
	}
  }
  else { 
      for (auto in : INofInst) { 
	if (!(compareToken(in.first,pointee))) {
		newINofInst.insert(std::make_pair(in.first, in.second));
	}
	else if ((compareToken(in.first,pointee)) and in.second != index) {  /* ob.[0] is different from ob.[1] */
		#ifdef PRINT
		errs() << "\n Token name same but field index not matching. ";
		#endif
		newINofInst.insert(std::make_pair(in.first, in.second));
	}
     }
  }//end else
  return newINofInst;
}

///Inserts the liveness information of the RHS into the IN 
B IPLFCPA:: insertRhsLin(B currentIN, std::vector<std::pair<Token*, int >> list, F forwardIN, fetchLR& ins)  {
   #if defined(TRACE) || defined(PRINT)
   errs() << "\n Inside function inInserter......";
   #endif
   B INofInst = currentIN;

   for (auto listValues : list)   {
       int  listValuesIndir = listValues.second;
       if (listValuesIndir == 0) { /* Rhs: ...=&u */
	    if (!ins.getGEP()) {
		#ifdef PRINT
		errs() << "\n Rhs is ...= &y ";		
		#endif
		return INofInst;
	    }
	    else {
		#ifdef PRINT
		errs() << "\n Rhs = &GEP. Instr is GEP so generate liveness of Rhs. ";
		#endif
		if (listValues.first->isValPointerType())
			INofInst.insert(std::make_pair(listValues.first,"")); 
		return INofInst;
	    }
       }//end if indir=0
       else if (listValuesIndir == 1) { /* Rhs: ...=y */
	    #ifdef PRINT
	    errs() << "\n Rhs is ...=y ";
	    #endif
	    if (ins.getBitcast()) /* Remove the field index*/
		    INofInst.insert(std::make_pair(listValues.first, ""));	
	    else
		    INofInst.insert(std::make_pair(listValues.first, listValues.first->getFieldIndex()));
	    return INofInst;
       }
       else if (listValuesIndir == 2) { /* Rhs: ...=*y */
	    #ifdef PRINT
            errs() << "\n Rhs is ...=*y ";
	    #endif
            std::queue<Token*> q;
	    std::queue<std::string> q1;
            q.push(listValues.first);
	    q1.push(listValues.first->getFieldIndex());

            while (listValuesIndir > 0 and !q.empty())  { 
		Token* listValuesTemp = q.front();
		std::string listIndx = q1.front();
                q.pop();  q1.pop();

                if (listValuesTemp->getName() != "NULL" and listValuesTemp->isValPointerType()) { 
	            INofInst.insert(std::make_pair(listValuesTemp, listIndx));
		    for (auto fIN : forwardIN) { 

			if (compareToken(fIN.first.first, listValuesTemp) and fIN.first.second == listIndx) { 
				B Pointee = fIN.second; 
				for (auto p : Pointee) {
				   if (!compareToken(p.first, dummy)) {
		                       	q.push(p.first); 
					q1.push(p.second);
				   }//inner if
				}//inner for
			}//end outer if
		    }//end outer for   
                }//end if 
		listValuesIndir--;
            }//end while
       }//end else if Rhs indir=2
  }//end for
  return INofInst;
}



B IPLFCPA::performMeetBackward(const B& d1_currOUT, const  B& d2_succIN) const  {
  errs() << "\n Inside performMeetBackward...................";
  std::set<std::pair<Token*, std::string>> retMeetOUTB = d1_currOUT;
  for (auto valueInSuccIN : d2_succIN)         // prevOUT merge succIN
           retMeetOUTB.insert(valueInSuccIN);
   return retMeetOUTB;
}

///Compares two TOKEN values
bool IPLFCPA::compareToken(Token* T1, Token* T2) const{
 errs() << "\n Inside compareToken....";
 if (T1->getName() == T2->getName() and T1->getMemTypeName() == T2->getMemTypeName()) 
	return true;
 return false;
}

bool IPLFCPA::EqualDataFlowValuesBackward(const B& d1, const B& d2) const{
   errs() << "\n Inside EqualDataFlowValuesBackward.................";
   if (d1.empty() and d2.empty())
	return true;
   else if ( (d1.empty() and !d2.empty()) or (!d1.empty() and d2.empty()))
	return false;
   else if (!d1.empty() and !d2.empty()) {
      for (auto a1 : d1) {
         Token* newToken = a1.first;
         std::string newInd = a1.second;
         bool vdiff = true;
	 for (auto a2 : d2) {
	     Token* prevToken = a2.first;
	     std::string prevInd = a2.second;
	     if (compareToken(newToken, prevToken) and newInd == prevInd) 
	         vdiff = false;
         }//end inner for
         if (vdiff)	
	     return false; //not equal
       }//end outer for
   }//end else
   return true; //equal	
}

F IPLFCPA::getBoundaryInformationForward() {
    errs() << "\n Inside getBoundaryInformationForward ";
    std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>> F_TOP;
    return F_TOP;
}

F IPLFCPA::getInitialisationValueForward() {
    errs() << "\n Inside getInitialisationValueForward ";
    std::map<std::pair<Token*, std::string>, std::set<std::pair<Token*, std::string>>> F_TOP;
    return F_TOP;
}

B IPLFCPA::getBoundaryInformationBackward() {
    errs() << "\n Inside getBoundaryInformationBackward ";
    std::set<std::pair<Token*, std::string>> B_TOP;
    return B_TOP;
}

B IPLFCPA::getInitialisationValueBackward() {
    errs() << "\n Inside getInitialisationValueBackward ";
    std::set<std::pair<Token*, std::string>> B_TOP;
    return B_TOP;
}

/*
* CHange functionPass to ModulePass
* Iterate over every function in the Module and call SLIM modeling functions to create the abstraction
* Update TransformIR to handle a call instr now.
* Global instr list should be printed. #GOAL
*/

class transIR : public ModulePass {
public:
  static char ID;
  transIR() : ModulePass(ID){}
  virtual bool runOnModule(Module &M)   {   
	
	//Module *M = F.getParent();
	lfcpaObj.setCurrentModule(&M);
 	errs() << "\n Splitting the BB..............."; 
	//lfcpaObj.startSplitting();	

	errs() << "\n Applying SLIM modeling..............#";
	for (Module::iterator ff=M.begin(), ef=M.end(); ef!=ff; ++ff) {
	    Function *F = &(*ff);
	    for (Function::iterator bb=F->begin(), e=F->end(); e!=bb; ++bb)  {
		BasicBlock* BB = &(*bb);
		lfcpaObj.simplifyIR(F,BB);
		lfcpaObj.setLhsRhsMap(F, BB);				    
	    }
	}
	lfcpaObj.printGlobalInstrList();
	errs() << "\n Executing VASCO........";
	lfcpaObj.doAnalysis(M);	
        return false;
  }
};

/*class transIR : public FunctionPass {
public:
  static char ID;
  transIR() : FunctionPass(ID){}
  virtual bool runOnFunction(Function &F)   {   
	
	Module *M = F.getParent();
	lfcpaObj.setCurrentModule(M);
 	errs() << "\n Splitting the BB..............."; 
	lfcpaObj.startSplitting();	
         if (F.getName() == "main") { 
	    errs()  << "\n Interprocedural LFCPA.....";
	    lfcpaObj.test();	   		
	}		
return false;
  }
};*/

char transIR :: ID = 0;
static RegisterPass<transIR> X(
	"lfcpa",		// the option name
	"lfcpa",	// option description
	false,
	false					
);

