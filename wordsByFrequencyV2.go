/*
The purpose of this application is to help learn the most used words first.
1) I extract all the words of the text and put them in descending order of use ( first the most used words)
2) for each word I list the sentences that contain it, but these can also be thousands, which ones to propose?
3) If I assume that the most used words must be studied firstly, I assume that those with greater frequency have all already been learned 
and those with less frequency are yet to be learned.
4) From what has been hypothesized above, I assume that the most interesting sentences to propose are those in which the number of unknown words is as low as possible
5) Concluding, for each word with frequency F I propose the sentences in increasing order of the number of words the frequency of which is lower than F

=============================
program logic:
1) split the text into rows
2) extract all the words of each row
3) associate to each word the number of lines that contain it (the frequency) and the index of these lines
4) list the words in reverse order of frequency of use (number of lines containing the word)
5) to each line associate the list of frequencies of its words
6) for each word to each line that contains it, associate the number of words with a lower frequency than this one
7) at each request a word to study, list some or all of the sentences that contain it, starting with those with the fewest unknown words (i.e. with frequency < of this word)
*/


package main

import (
	//"time"
	"fmt"
	"log"
	"os"
	"os/signal"
	"time"
	"runtime"
    "strings"
	"strconv"
	"encoding/hex"
    "regexp"
    "sort"
    "bufio"	
    "github.com/zserge/lorca"	
	"github.com/lxn/win"
	
)


//----------------------------------
var timeBegin  = time.Now()
var totElapsed = 13.283031 

var lastPerc=0; 
var prevPerc = -1; 
//---------------
var	html_path        string = "WBF_html_jsw"
var inputFileList    string = "inputFileList.txt";     // file listing all input files 
var langFile         string = "language.txt"           // lang and voice file    
//-----------
var inpParaFile = "" ; //  inp_lemma_paradigma_example.csv";  


var outFile          = "outFileProva.csv" 
//------------
var dictionaryFolder string = ""  //   prevRunDictionaryAndVoice";
var inpLemmaFile        string = ""  //   lemma_file.txt";  
var inpLemmaFile2       string = ""  //   lemma_file.txt"  aggiunto  
var sw_rewrite_wordLemma_dict bool = false
var sw_rewrite_word_dict bool = false
var sw_rewrite_row_dict  bool = false
var outWordLemmaDict_file = "newWordLemmaDict.txt";
var outLemmaTranDict_file = "newLemmaTranDict.txt"
var outLemmaNotFound      = "newLemmaNotFound.txt"

var outRowDict_file  = "newRowDict.txt"
var sw_ignore_newLine bool = false
var sw_nl_only        bool = false
//------------------------------------
const wSep = "§";                         // used to separe word in a list 
const endOfLine = ";;\n"
//const LAST_WORD0 = "zzz";
const LAST_WORD = "\xff\xff\xff"

const LAST_WORD_FREQ = 999999999 
//---------------------
var righe      =  []string{} 
//------------
//------
var parameter_path_html string  = "WBF_html_jsw"
//------------------

type rowStruct struct {
    rRow1        string
	rNfile1      int  
	rSwExtra     bool 
    rNumWords    int
	rListIxUnF   []int 
	rListFreq    []int   
	rTran1       string 
}


//--
type wordStruct struct {       // a word is repeated several time one for each row containing it  
	wWordCod  string
    wWord2    string
	//sw_ignore bool
	wIxUniq   int               // index of uniqueWordByFreq      
	wNfile    int 
    wIxRow    int       
	wIxPosRow int 
	wTotRow   int 
	wTotMinRow int
	wTotWrdRow int 
}
//--
type wordIxStruct struct {
	uWordCod    string	
    uWord2      string	
	uIxUnW      int            // index of this word in the uniqueWordByFreq	
	uIxUnW_al   int            // index of this word in the uniqueWordByAlpha 	
	uTotRow     int 
    uIxWordFreq int            // index of this word in the wordSliceFreq	
	uLemmaL    []string       // list of lemma 
	uTranL     []string       // list of translation    
	uLevel     []string  
	uPara      []string  
	uExample   []string  
	//outStr += oRiga + wL.dL_level[m] + "|" + 	wL.dL_para[m] + "|" + wL.dL_example[m] 	+ "\n"
}	
//---
type lemmaStruct struct {
	lWordCod string 
	lWord2   string 
	lLemma   string
} 
//---
type wDictStruct struct {
	dWord  		string 
	dIxWuFreq 	int 
	dLemmaL     []string 
	dTranL      []string 	
} 
//---
type rDictStruct struct {
	rdIxRow  int 
	rdTran   string 
} 
//---------------
type statStruct struct {
	uniqueWords  int 
	uniquePerc   int 
	totWords  int
	totPerc   int 
}
//--------------------------
type lemmaTranStruct struct {
	dL_lemmaCod  string 
	dL_lemma2    string 
	dL_tran     string 
	dL_level    string
	dL_para     string	
	dL_example  string	
} 
//---------------
type lemmaWordStruct struct {
	lw_lemmaCod string 	
	lw_lemma2   string 	
	lw_word  string 
	lw_ix    int
}
//------------
type paraStruct struct {
	p_lemma    string	
	p_level    string
	p_para     string
	p_example  string 
}	
//-----------------
var lemmaNotFoundList = make([]string,0,100)
//----------------------
var level_other = "-oth-"
var list_level_str = " " + level_other + " A0 A1 A2 B1 B2 C1 C2 "
var list_level          = make([]string,0, 0) 
var only_level_numWords = make([]int,   0, 0)  
var perc_level          = make([]int,   0, 0)  
//-------------------------------------------
var separRow   = "[\r\n.;:?!]";
//var separRowFalse = "[\r\n]";
var separWord = "["     +
			"\r\n.;?!" + 
			"\t"       +
			" "        + 
			",:"       +
			"\\-"      + 
			"_"        +
			"\\+"      +
			"\\*"      +
			"()<>"     + 
			"\\]\\["   +
			"`{}«»‘’‚‛“””„‟" +		
			"\""       + 
			"'"        + 	
			"\\/"      +  
			wSep       + 
			"]" ; 	
var separRowList = make([]string,0,0)		
//----------------------------------------		
/**
 	var percA0  int = 0 
	var percA1  int = 0
	var percA2  int = 0 
	var percB1   int = 0 
	var percOth  int = 0 
 
var only_A0 int = 0  
var only_A1 int = 0  
var only_A2 int = 0     
var only_B1 int = 0      
var only_Ot int = 0    	
***/

var msgLevelStat = "" 


var wordSliceAlpha = make([]wordStruct, 0, 0)  
var wordSliceFreq  = make([]wordStruct, 0, 0)  


var uniqueWordByFreq  []wordIxStruct;   // elenco delle parole in ordine di frequenza
var uniqueWordByAlpha []wordIxStruct;   // elenco delle parole in ordine alphabetico

var newWordLemmaPair    [] lemmaStruct // all word-lemma pair 


var dictLemmaTran []lemmaTranStruct ;  // dictionary lemma translation  
var lemma_word_ix []lemmaWordStruct  

//var wordStatistic_un =  make( []statStruct, 101, 101);	
var wordStatistic_tx =  make( []statStruct, 101, 101);	
var inputTextRowSlice       []rowStruct;
var isUsedArray    []bool
var countNumLines  bool = false 
var maxNumLinesToWrite = 0

//var rowArrayByFreq []rowStruct;
//-------------------------------

var dictionaryWord = make([]wDictStruct,0,0);  
var numberOfDictLines =0;  
var dictionaryRow  = make([]rDictStruct,0,0);  
var numberOfRowDictLines =0;  
var prevRunLanguage = ""; 
//var prevRunListFile = "" 
//-----------
var wordLemmaPair    [] lemmaStruct // all word-lemma pair  
var numLemmaDict int =0 
//var result_row1  string; 
//var result_word1 string;
//var result_word2 string;  
var numberOfRows  = 0; 
var numberOfWords = 0; 
var numberERRORS=0
var numberOfUniqueWords = 0; 
var showReadFile string = ""
//--------------------------------------------------------
var scrX, scrY int = getScreenXY();

var sw_stop bool = false
var errorMSG = ""; 
var sw_begin_ended = false     
var sw_HTML_ready  = false     
//--------------------------------

//--------------------------

var lemma_para_list = make([]paraStruct, 0, 0 )   	

//--------------------------
//---
var fseq = "z§" ; 
var lenFseq = len(fseq) 
//--------------------------
//--------------------------------
func check(e error) {
    if e != nil {
        panic(e)
    }
}

//-------------------------------
func getPgmArgs( key0, key1 , key2 , key3 string) (string, string, bool, int) {  
	
	//  getPgmArgs("-html", "-input" , "-countNumLines" ,  "-maxNumLinesToWrite")	

	args1    :=  os.Args[1:]		
	
	
	var val0, val1, val2, val3 string
	for a:=0; a < (len(args1)-1); a++ {
		switch args1[a] {
			case key0 :   val0 = args1[a+1]
			case key1 :   val1 = args1[a+1]
			case key2 :   val2 = args1[a+1]
			case key3 :   val3 = args1[a+1]
		}
	}  
	var isCount = false;
	if strings.TrimSpace(val2) == "true" {
		isCount = true
	}
	var num=0; 
	num, err := strconv.Atoi( strings.TrimSpace(val3) )
	if err != nil {
		num=0
	}

	//fmt.Println("args=", args1,  " val0=", val0, " val1=", val1, " val2=", val2 , " val3=", val3, " num=", num)   
	
	return val0, val1, isCount, num
} // end of getPgmArgs

//============================================

var ui, err = lorca.New("", "", scrX, scrY); // crea ambiente html e javascript  // if height and width set to more then maximum (eg. 2000, 2000), it seems it works  

//============================================
func main() {
	val0, val1, val2, val3 := getPgmArgs("-html",  "-input" , "-countNumLines" , "-maxNumLinesToWrite")	
	countNumLines      = val2
	maxNumLinesToWrite = val3
	
	if val0 != "" { parameter_path_html = strings.ReplaceAll(val0,"\\","/")  } 
	if val1 != "" { inputFileList       = strings.ReplaceAll(val1,"\\","/")  }  	
	
	fmt.Println("\n"+ "parameter_path_html =" + parameter_path_html + "\n" +  "input = " + inputFileList )
	fmt.Println("countNumLines       = " ,  countNumLines)
	//fmt.Println("maxNumLinesToWrite = " , maxNumLinesToWrite) 
	fmt.Println("\n----------------\n")
	
	//------------------------------
	args := []string{}
	if runtime.GOOS == "linux" {
		args = append(args, "--class=Lorca")
	}
	//  err := lorca.New("", "", 480, 320, args...) moved out of main so that ui is available outside main()
	if err != nil {
		log.Fatal(err)
	}
	defer ui.Close()
	
	get_all_binds()  //  binds inside are executed asynchronously after calling from js function (html/js are ready) 
	
	begin();  // this function is  executed firstily before html/js is ready  
	fmt.Println("END of begin()") 
	// the following in main() is executed at the end when the browser is close 
	// Wait until the interrupt signal arrives or browser window is closed
	sigc := make(chan os.Signal)
	signal.Notify(sigc, os.Interrupt)
	select {
		case <-sigc:
		case <-ui.Done():
	}
	log.Println("exiting...")
}
// =================================

func get_all_binds() {
		
			progressivePerc(true,   1 ,"0-bind1") 
		
		// A simple way to know when UI is ready (uses body.onload event in HTML/JS)
		ui.Bind("goStart", func() { 
				fmt.Println("Bind goStart   sw_begin_ended=", sw_begin_ended); 
				sw_HTML_ready = true 
				if sw_begin_ended {
					bind_goStart()
				}	
			} )
			progressivePerc(true,   1 ,"1-bind") 			
		//--------------
		ui.Bind("go_passToJs_wordList", func(fromWord int, numWords int, sel_level string, js_function string) {
				bind_go_passToJs_wordList(fromWord,  numWords, sel_level, js_function)  })
			progressivePerc(true,   1 ,"2-bind") 				
		//--------------------------------------		
		ui.Bind("go_passToJs_prefixWordList", func(numWords int, wordPrefix string, js_function string) {
				bind_go_passToJs_prefixWordList( numWords, wordPrefix, js_function) } ) 
			progressivePerc(true,   1 ,"3-bind") 
		//--------------------------------------		
		ui.Bind("go_passToJs_betweenWordList", func(maxNumWords int, fromWordPref string, toWordPref string, js_function string) {
				bind_go_passToJs_betweenWordList( maxNumWords, fromWordPref, toWordPref, js_function) } ) 		 			
		//---------------------------------------
		ui.Bind("go_passToJs_lemmaWordList", func(lemma string, js_function string) {
				bind_go_passToJs_lemmaWordList(lemma, js_function) } ) 
			progressivePerc(true,   1 ,"4-bind") 	
		//---------------------------------------
		ui.Bind("go_passToJs_getWordByIndex", func( ixWord int, maxNumRow int, js_function string) {
				bind_go_passToJs_getWordByIndex( ixWord, maxNumRow, js_function) } ) 
			progressivePerc(true,   1 ,"5-bind") 	
		//---------------------------------------
		ui.Bind("go_passToJs_thisWordRowList", func( aWord string, maxNumRow int, js_function string) {
				bind_go_passToJs_thisWordRowList( aWord, maxNumRow, js_function) } )
			progressivePerc(true,   1 ,"6-bind") 			
		//---------------------------------------
		ui.Bind("go_passToJs_rowList", func( inpBegRow int, maxNumRow int, js_function string) {
				bind_go_passToJs_rowList( inpBegRow, maxNumRow, js_function) } )
			progressivePerc(true,   1 ,"7-bind") 			
		//---------------------------------------
		ui.Bind("go_passToJs_rowWordList", func( numIdOut string, numId int, js_function string ) {
				bind_go_passToJs_rowWordList(numIdOut, numId, js_function) } ) 	
			progressivePerc(true,   1 ,"8-bind") 					
		//---------------------------------------	
		ui.Bind("go_write_lang_dictionary", func( langAndVoiceName string) {
			bind_go_write_lang_dictionary( langAndVoiceName ) } )  
			progressivePerc(true,   1 ,"9-bind") 	
		//---------------------------------------	
		ui.Bind("go_write_word_dictionary", func( listGoWords string) {
			bind_go_write_word_dictionary( listGoWords ) } )  
			progressivePerc(true,   1 ,"10-bind") 					
		//---------------------------------------			
		ui.Bind("go_write_row_dictionary", func( listGoRows string) {
			bind_go_write_row_dictionary( listGoRows ) } )  
			progressivePerc(true,   1 ,"11-bind") 			
		//------
}  

//---------------------------------------------
func bind_goStart() {
		fmt.Println("\nXXXXXXX GO XXXXXXX  goStart xxxxxxxxxxxxx è stato lanciato da 'onload()' nel file  HTML\n" );  
		//fmt.Println("\nXXXXXXX GO XXXXXXX  buildStatistics() xxxxxxxxxxxxx " );  	
		
		buildStatistics()
		
		mainNum := strconv.Itoa(numberOfUniqueWords) +";" + strconv.Itoa(numberOfWords) + ";" + strconv.Itoa(numberOfRows) +		   
		   ";" + "level " + msgLevelStat + "))" 		
		
		go_exec_js_function("js_go_showReadFile", mainNum + showReadFile);  
		
		fmt.Println("\nXXXXXXX GO XXXXXXX  js_go_ready() xxxxxxxxxxxxx " );  
		
		if sw_stop { 
			errorMSG = strings.ReplaceAll( errorMSG, "\n"," ") 
			go_exec_js_function( "js_go_setError", errorMSG ); 	
			log.Println("UI is ready ( run stopped because of some error)")
		} else {
			go_exec_js_function("js_go_ready", prevRunLanguage)  // +"<file>" + prevRunListFile); 
			log.Println("UI is ready")
		}
} // end of bind_goStart
 
//----------------------------------------

func bind_go_passToJs_wordList(fromWord int, numWords int, onlyThisLevel string, js_function string) {
		
		var from1, to1 int; 
		from1 = fromWord; //   - 1; 
		if (from1 < 1) {from1=1;}
		if (from1 >= numberOfUniqueWords) {from1 = numberOfUniqueWords - 1;}		
		to1 = numWords + from1; 
		if (to1 > numberOfUniqueWords)   {to1 = numberOfUniqueWords;}	 
				
		//var xWordF wordIxStruct;  
		var outS1 string = ""; 
		//var row11 string;
		//var numNoTran = 0
		
		//console("bind_go_passToJs_wordList() 0 "  ) 	
		
		for i:= from1; i < to1; i++ { 
			sw, rowW := word_to_row( onlyThisLevel, uniqueWordByFreq[i] )  
			if sw {	
				outS1 += rowW 
			}  				 
		}			
		//row11 = ",-1," +  strconv.Itoa( numNoTran) + ",numNoTran";   	
		//outS1 += strings.TrimSpace( row11 ); 
		
		go_exec_js_function( js_function, outS1 ); 	
	
		//go_exec_js_function( js_function, strings.ReplaceAll( outS1, "`", " ")); //   outS1 ); 	
					
}  // end of bind_go_passToJs_wordList	

//------------------------------------------------------

func word_to_row( onlyThisLevel string, xWordF2 wordIxStruct) (bool, string)  {
	
	sw:= false
	
	if onlyThisLevel == "any" {
		sw = true
	} else {
		if len(	xWordF2.uLevel) > 0  {
			// first level of the first lemma  
			levels:= strings.Split( xWordF2.uLevel[0], "|" )
			level3 := strings.TrimSpace( levels[0] )
			if len(level3) > 0 {
				sw = ( onlyThisLevel == levels[0] ) 		
				if sw == false {	
					if onlyThisLevel == level_other {  // se cerco -oth- 
						if level3 == "" {  // questo if dovrebbe essere superfluo 
							sw = true
						} else {
							level3:= " " + level3 + " "
							if strings.Index( list_level_str, level3 ) < 0  {sw = true}  // se il livello non è tra quelli previsti allora è other 
						}
					}
				}
			} else {  // level is missing, in case the required level is -oth-,   this word must be included ( ie. sw = true)
				 sw = ( onlyThisLevel == level_other )  
			} 
		}  
	}
	//-----------
	if sw {   
		return sw, xWordF2.uWordCod + ";." + xWordF2.uWord2+ ";." + 
					strconv.Itoa(xWordF2.uIxUnW) + ";." + strconv.Itoa(xWordF2.uTotRow)  + ";." + 
					fmt.Sprint( strings.Join(xWordF2.uLemmaL,  wSep)  ) + ";." + 
					fmt.Sprint( strings.Join(xWordF2.uTranL,   wSep)  ) + ";." +  
					fmt.Sprint( strings.Join(xWordF2.uLevel,   wSep)  ) + ";." +  
					fmt.Sprint( strings.Join(xWordF2.uPara,    wSep)  ) + ";." +  
					fmt.Sprint( strings.Join(xWordF2.uExample, wSep)  ) + ";." +  
					endOfLine 
	} else {
		return sw, ""
	}				 
} // end of word_to_row 

//--------------
func TOGLIbind_go_passToJs_prefixWordList( numWords int, wordPrefix string, js_function string) {

		var onlyThisLevel string = "any" ; // "A0"  // questo deve arrivare da parametro  
		
		var outS1 string; 
		from1, to1 := searchAllWordWithPrefixInAlphaList( wordPrefix )
		//var row11 string;
		fmt.Println( "go_passToJs_prefixWordList =", wordPrefix, ", ret da search... from1=" , from1 , "  to1=", to1)
		//var numNoTran = 0   
		if (to1 < 0) {
			outS1 = "NONE," + wordPrefix ; // nessuna parola che inizia con " + wordPrefix;
		} else {	
			//zz:=0
			for i:=from1; i <=to1; i++ {
				//outS1 += word_to_row( onlyThisLevel, uniqueWordByAlpha[i] )  	
				sw, rowW := word_to_row( onlyThisLevel,  uniqueWordByAlpha[i] )  	  
				if sw {	
					outS1 += rowW 
				}  	
				
			}
		}
		//row11 = ",-1," +  strconv.Itoa( numNoTran) + ",numNoTran";   	
		//outS1 += row11 ; 
		
		//fmt.Println( "go_passToJs_prefixWordList chiama go_exec_js_function( " + js_function + ", outS1=" + outS1);  
		
		go_exec_js_function( js_function, outS1 ); 		
	
			
} // end of TOGLIbind_go_passToJs_prefixWordList

//--------------

func bind_go_passToJs_prefixWordList( numWords int, wordPrefix string, js_function string) {
	
	bind_go_passToJs_betweenWordList( numWords, wordPrefix, wordPrefix, js_function) 
			
} // end of bind_go_passToJs_prefixWordList
//-----------------------------------------

func bind_go_passToJs_betweenWordList( maxNumWords int, fromWordPref string, toWordPref string, js_function string) {
	
	/**
	var uno = LAST_WORD0
	var due = LAST_WORD
	fmt.Println( "(uno=", uno , " > ", " due=",  due, ") = ",  ( uno > due ) );     
	**/
	var onlyThisLevel string = "any" ; // "A0"  // questo deve arrivare da parametro  
	var outS1 string; 	
	
	fromWord := strings.ToLower(strings.TrimSpace( fromWordPref ));  
	fromWordCod:= newCode(fromWord)		
	from1, _:= lookForWordInUniqueAlpha( fromWordCod)	
	//--
	toWordPref2:= toWordPref + LAST_WORD
	toWord := strings.ToLower(strings.TrimSpace( toWordPref2 ));  
	toWordCod:= newCode(toWord)		
	_,   to2:= lookForWordInUniqueAlpha( toWordCod)	
	//--
	if from1 < 0 { from1=0} 
	if to2  >=  len(uniqueWordByAlpha) { to2 =  len(uniqueWordByAlpha) - 1 } 
	//---
	toWordCod += LAST_WORD
	num1:=0
	for i:=from1; i <=to2; i++ {		
		sw, rowW := word_to_row( onlyThisLevel,  uniqueWordByAlpha[i] )  	  
		if sw == false { continue}	
		j1 := strings.Index(rowW, ";.") 
		if rowW[0:j1] < fromWordCod { continue}	
		if rowW[0:j1] > toWordCod { break}	
		num1++
		if num1 > maxNumWords { break }
		outS1 += rowW 	
	}
	go_exec_js_function( js_function, outS1 ); 		
	
			
} // end of bind_go_passToJs_betweenWordList


//----------------------------------------------
func bind_go_passToJs_lemmaWordList(lemmaToFind0 string, js_function string)   {
		lemmaCod:= newCode( lemmaToFind0 )
		var onlyThisLevel string = "any" ; // "A0"  // questo deve arrivare da parametro  
		
		outS1 := "" 
				
		fromIxX, _ := lookForLemmaWord( lemmaCod )
		
		fromIx:= fromIxX
		for k:= fromIxX; k >= 0; k-- {
			if lemma_word_ix[k].lw_lemmaCod < lemmaCod { break }
			fromIx = k
		}
		for k:= fromIx; k < len(lemma_word_ix); k++ {
		
			if lemma_word_ix[k].lw_lemmaCod == lemmaCod {		
				ix := lemma_word_ix[k].lw_ix 	
				//outS1 += word_to_row( onlyThisLevel,  uniqueWordByFreq[ix] ) 	
				sw, rowW := word_to_row( onlyThisLevel, uniqueWordByFreq[ix] )  
				if sw {	
					outS1 += rowW 
				}  					
			} else {
				if lemma_word_ix[k].lw_lemmaCod > lemmaCod { break }
			}
		} 
		if len(outS1)< 3 {
			outS1 = "NONE," + lemmaToFind0; 			
			//fmt.Println(" bind_go_passToJs_lemmaWordList() ", outS1) 
		} 	
		
		go_exec_js_function( js_function, outS1 ); 		
				
} // end of bind_go_passToJs_lemmaWordList

//-----------------------------------------------------------

func bind_go_passToJs_getWordByIndex( ixWord int, maxNumRow int, js_function string) {
		
		if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}	
		
		var xWordF     = uniqueWordByFreq[ixWord]  	
		aWord:= xWordF.uWord2; 
		
		bind_go_passToJs_thisWordRowList( aWord, maxNumRow, js_function)
		
} // end of bind_go_passToJs_getWordByIndex

//----------------------------------------
func TOGLI2bind_go_passToJs_getWordByIndex( ixWord int, maxNumRow int, js_function string) {
		
		var outS1 string; 
		//ixWord--; 
		if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}	
		
		var xWordF     = uniqueWordByFreq[ixWord]   
		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNumRow; 		
		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
		
		/**
		word   lemma: lemma1:  paradigma 
			
		????anto123
		**/
		header:= "<HEADER>\n" + "<WORD>" + xWordF.uWord2 + "</WORD>"
		
		hd_tr := "<TABLE>\n"	
		for z:=0; z < len(xWordF.uLemmaL); z++  {
			hd_tr += "<tr><td class=\"wBold\">" + xWordF.uWord2 + "</td><td>"
			if xWordF.uPara[z] == "" {	hd_tr += xWordF.uLemmaL[z]+"</td>"} else {hd_tr += xWordF.uPara[z] + "</td>"} 
			hd_tr += "<td class=\"c_tran\">" + xWordF.uTranL[z] + "</td></tr>\n"	
		}	
		hd_tr += "</TABLE>\n" 
		header += hd_tr
		header += "</HEADER>"
		
		//fmt.Println("HEADER = \n", header) 
		
		outS1 += header 
		/**
		preRow := xWordF.uWord2 + ";" + strconv.Itoa(xWordF.uIxUnW) + ";" + strconv.Itoa(xWordF.uTotRow)  + ";" 
		lemmaList := xWordF.uLemmaL
		tranList  := xWordF.uTranL
		for z:=0; z < len(lemmaList); z++  {
			//row11 := preRow +  lemmaList[z]+ "," + tranList[z] + ";"
			outS1 += preRow +  lemmaList[z]+ ";" + tranList[z] + endOfLine 
		}	
		***/
		
		
		preIxRR := -1
		/*
		here are scanned all the rows containing the word required (with index ixWord) 
		for each line totMinRow is the number of words in the line with lower reference than the required word (ie. not studied yet)	
		*/
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			ixRR:= wS1.wIxRow
			if (ixRR == preIxRR) { continue;} 
			preIxRR = ixRR; 
			if ixRR >= numberOfRows { continue;} // actually there  must be some error here 
			
			rline := inputTextRowSlice[ixRR]
			rowX := rline.rRow1					
			outS1 += "<br>;;" + strconv.Itoa(wS1.wNfile) + ";;" + strconv.Itoa(wS1.wIxRow) +				
				 ";; " + cleanRow(rowX) + ";; " + rline.rTran1; 				
		} 	
		
		go_exec_js_function( js_function, outS1 ); 	
		
}   // end of TOGLI2bind_go_passToJs_getWordByIndex 

//----------------------------------------------

//----------------------------------------------
func bind_go_passToJs_thisWordRowList( aWord string, maxNumRow int, js_function string) {    // NEW 
	
	//  lista tutte le frasi che contengono le parole con lemma della parola cercata 
	//fmt.Println("bind_go_passToJs_thisWordLemmaWordRowList() 1  aWord=", aWord )
    
	//  1) from the word get all lemma 
	// 	2) from each lemma get all words 
	//  3) from each word all row
	//------------------
	
	var outS1 string;
	
	//---------------------------------------
	//  1) from the word get all lemma 
	//-------	
	var xWordF wordIxStruct;  		
	wordCod:= newCode( aWord )		
	ixF, ixT:= lookForWordInUniqueAlpha( wordCod)	
	if (ixT < 0) {
			outS1 += "NONE," + aWord  
			go_exec_js_function( js_function, outS1 ); 	
	} 
	//----
	lemmaList1:= make([]string,0,10)
	for ix:= ixF; ix <= ixT; ix++ {
		xWordF =  uniqueWordByAlpha[ix] 
		if xWordF.uWordCod != wordCod { continue }  
		ixWord := xWordF.uIxUnW			
		if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}		
		xWordF     = uniqueWordByFreq[ixWord] 
		for z:=0; z < len(xWordF.uLemmaL); z++  {
			lemmaList1 = append(lemmaList1, newCode( xWordF.uLemmaL[z]) ) 
		}			
	}
	if len(lemmaList1) < 1 { 
			outS1 += "NONE," + aWord  
			go_exec_js_function( js_function, outS1 ); 	
	} 
	//----   
	sort.Strings(lemmaList1)
	
	//fmt.Println("bind_go_passToJs_thisWordLemmaWordRowList() 2  lemmaList1=", lemmaList1 )
	
	//-----------------
	//  2) from each lemma get all words 
	//
	preL:= ""
	lemWordList2 := make([]lemmaWordStruct, 0, 10)  
	var wL2 lemmaWordStruct;
	for _, lemma1Cod:= range( lemmaList1 ) {
		if lemma1Cod == preL { continue }
		preL = lemma1Cod	
		fromIxX, _ := lookForLemmaWord( lemma1Cod )		// ??? se non trova cerca lemma1Cod fino al punto.
		fromIx:= fromIxX
		for k:= fromIxX; k >= 0; k-- {
			if lemma_word_ix[k].lw_lemmaCod < lemma1Cod { break }
			fromIx = k
		}
		for k:= fromIx; k < len(lemma_word_ix); k++ {
			if lemma_word_ix[k].lw_lemmaCod != lemma1Cod { continue	}   	// ???nov se non trova cerca lemma1Cod fino al punto.
			wL2 = lemma_word_ix[k]	
			wL2.lw_word = newCode( wL2.lw_word )
			lemWordList2 = append( lemWordList2, wL2 )
		} 		
	}	
	//----
	
	fun_wordListToRowList_head( lemWordList2, maxNumRow, js_function) 	
				
} // end of XXbind_go_passToJs_lemmaRowList

//-----------------------------------------------------------

func fun_wordListToRowList_head( lemmaList []lemmaWordStruct, maxNumRow int, js_function string) {
		
	maxNumRow0 := maxNumRow;	
	listWords:= ""
	//hd_tr := "<TABLE>\n"	
	hd_tr := ""; 
	
		preL :=""	
		preW :=""
		line2:=""
		
	listIxRR := make([]int,0, 110)
	
	for _, lemmaX := range(lemmaList) { 	
		ixWord:= lemmaX.lw_ix
		var xWordF     = uniqueWordByFreq[ixWord]   
		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNumRow; 		
		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
		
		listWords += " " +  xWordF.uWord2
		for z:=0; z < len(xWordF.uLemmaL); z++  {
			newL:= xWordF.uLemmaL[z]
			if newL != lemmaX.lw_lemma2 { continue }   // ???nov    newCode???    ( sto c3ercando frasi doppie 
			newT:= xWordF.uTranL[z]			
			newP:= xWordF.uPara[z]
			if newL == preL { 
				newL=""
				newT=""
				if preW != xWordF.uWord2 { 
					hd_tr += xWordF.uWord2 + " ";  
					preW = xWordF.uWord2
				} 
			} else { 
				if newP == "" {
				    newP = newL;
					line2 = "&nbsp;&nbsp;&nbsp;&nbsp;"  	
				} else {
					line2 = "<br>"
				}
				preL = newL 
				if hd_tr != "" { hd_tr += "</td></tr>\n" 	}
				hd_tr += "<tr><td colspan=\"2\">" + "<span  class=\"c_lemma\">"  + newP + "</span>" + line2 + 
					"<span class=\"c_tran\">" + newT + "</span></td></tr>\n"	
				hd_tr += "<tr><td class=\"c_word\" style=\"width:2em;\">&nbsp;</td><td class=\"c_word\">" + xWordF.uWord2 + " " 
				preW =  xWordF.uWord2
			} 
			
		}

		list3:= fun_wordListToRowList_dett(ixWord, maxNumRow0)	
		for n1:=0; n1 < len(list3); n1++ {
			listIxRR  = append(listIxRR, list3[n1] )
		}			
				
	}
	hd_tr += "</td></tr>\n" 
	
	sort.Ints(listIxRR)  
	preIxRR:=0 
	outS1:= ""
	for n1:= 0; n1 < len(listIxRR); n1++  {
		ixRR := listIxRR[n1]
		if (ixRR == preIxRR) { continue;} 
		preIxRR = ixRR; 
		if ixRR >= numberOfRows { continue;} // actually there  must be some error here 		
		rline := inputTextRowSlice[ixRR]
		outS1 += "<br>;;" + strconv.Itoa(rline.rNfile1) + ";;" + strconv.Itoa(ixRR) +				
			 ";; " + cleanRow(rline.rRow1) + ";; " + rline.rTran1; 
	} 	
	header:= "<HEADER>\n" + "<WORD>" + strings.TrimSpace(listWords) + "</WORD>"
	header += "<TABLE style=\"padding: 0 2em;border:1px solid black;\">\n" + hd_tr + "</TABLE>\n" 
	header += "</HEADER> \n"
	
	go_exec_js_function( js_function, header + outS1 ); 	
	
}		

//-------------------------------
func fun_wordListToRowList_dett( ixWord int, maxNumRow int) []int {
		
		var xWordF     = uniqueWordByFreq[ixWord]   
		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNumRow; 		
		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
				
		/*		
		here are scanned all the rows containing the word required (with index ixWord) 
		for each line totMinRow is the number of words in the line with lower reference than the required word (ie. not studied yet)	
		*/
		
		listIxRR := make([]int,0, ixToList-ixFromList)
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			listIxRR = append( listIxRR, wS1.wIxRow) 			
		} 	
		return listIxRR

} // end fun_wordListToRowList
//-------------------------------
func TOGLIfun_wordListToRowList_dett( ixWord int, maxNumRow int) (int, string) {
		var outS1 = ""
		var xWordF     = uniqueWordByFreq[ixWord]   
		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNumRow; 		
		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
		
		preIxRR := -1
		/*
		here are scanned all the rows containing the word required (with index ixWord) 
		for each line totMinRow is the number of words in the line with lower reference than the required word (ie. not studied yet)	
		*/
		newL:=0 
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			ixRR:= wS1.wIxRow
			if (ixRR == preIxRR) { continue;} 
			preIxRR = ixRR; 
			if ixRR >= numberOfRows { continue;} // actually there  must be some error here 
			
			rline := inputTextRowSlice[ixRR]
			rowX := rline.rRow1					
			outS1 += "<br>;;" + strconv.Itoa(wS1.wNfile) + ";;" + strconv.Itoa(wS1.wIxRow) +				
				 ";; " + cleanRow(rowX) + ";; " + rline.rTran1; 
			newL++		
		} 	
		return newL, outS1

} // end TOGLIfun_wordListToRowList
//--------------------------------------------------
func bind_go_passToJs_thisWordRowListOLD( aWord string, maxNumRow int, js_function string) {  // OLD 
	// lista  tutte le frasi che contengono la parola indicata 
	
	var outS1 string;
	
	outS1 = fun_rowsWithThisWord( aWord, maxNumRow) // 1

	go_exec_js_function( js_function, outS1 ); 	
			
}   // end of bind_go_passToJs_thisWordRowList 

//---------------------------------------------------------------------
func fun_rowsWithThisWord( aWord string, maxNumRow int) string  {             
	
		// estrae  tutte le frasi che contengono la parola indicata 
		//fmt.Println(" in go esegue go_passToJs_thisWordRowList( aWord=", aWord, " maxNumRow=" , maxNumRow);  
		
		var outS1 string;
		
		//fmt.Println( "cerca ", aWord);
		
		var xWordF wordIxStruct;  
		//ixF, ixT := searchOneWordInAlphaList( aWord ) 
		
		wordCod:= newCode( aWord )		
		ixF, ixT:= lookForWordInUniqueAlpha( wordCod)	
		
		if (ixT < 0) {
			//fmt.Println( aWord, "\t NOT FOUND "); 
			outS1 += "NONE," + aWord  
			return outS1
		} 
		//---
		for ix:= ixF; ix <= ixT; ix++ {
			xWordF =  uniqueWordByAlpha[ix] 
			if xWordF.uWordCod != wordCod { continue }  
			ixWord := xWordF.uIxUnW	
			
			if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}	
			
			xWordF     = uniqueWordByFreq[ixWord]   
			
			var ixFromList = xWordF.uIxWordFreq 
			var ixToList   = ixFromList + xWordF.uTotRow;
			var maxTo1     = ixFromList + maxNumRow; 		
			
			if ixToList > maxTo1        { ixToList = maxTo1; }
			if ixToList > numberOfWords { ixToList = numberOfWords; }	
							
			preRow := xWordF.uWord2 + ";" + strconv.Itoa(xWordF.uIxUnW) + ";" + strconv.Itoa(xWordF.uTotRow)  + ";" 
			lemmaList := xWordF.uLemmaL
			tranList  := xWordF.uTranL
			for z:=0; z < len(lemmaList); z++  {
				outS1 += preRow +  lemmaList[z]+ ";" + tranList[z] + endOfLine 
			}	
			
			/**
			row11  := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" + 
					 fmt.Sprint( strings.Join(xWordF.uLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.uTranL, wSep) ) + endOfLine 
	
			//row11 := xWordF.word + "," + strconv.Itoa(xWordF.ixUnW) + "," + strconv.Itoa(xWordF.totRow)  + ";" + 
			//	fmt.Sprint( strings.Join(xWordF.uLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.uTranL, wSep)) + endOfLine   	
			outS1 += row11  			
			***/
			
			//outS1 += xWordF.word + ";" 
			//outS1 += " totRow=" + strconv.Itoa(xWordF.totRow) + " pos=" + strconv.Itoa( ixToList ) + ";" ; 
			nn:=0
			preIxRR := -1
			/*
			here are scanned all the rows containing the word required (with index ixWord) 
			for each line totMinRow is the number of words in the line with lower reference than the required word (ie. not studied yet)	
			*/
			//perc_unknown := 0;
			for n1 := ixFromList; n1 < ixToList; n1++  {
				wS1 := wordSliceFreq[n1] 
				ixRR:= wS1.wIxRow
				if (ixRR == preIxRR) {continue;} 
				preIxRR = ixRR; 
				nn++;
				if ixRR >= numberOfRows { continue;} // actually there  must be some error here 
				rline := inputTextRowSlice[ixRR]
				rowX := rline.rRow1		
		
				outS1 += "<br>;;" + strconv.Itoa(wS1.wNfile) + ";;" + strconv.Itoa(wS1.wIxRow) +
					 ";; " + cleanRow(rowX) + ";; " + rline.rTran1;  
			}
			
		} // end for ix	
		
		return outS1
		
}   // end of fun_rowsWithThisWord 

//-----------------------------------------------------

func bind_go_passToJs_rowList( inpBegRow int, maxNumRow int, js_function string) {
	// lista tutte le frasi richieste ( numero della prima frase, numero di frasi) 
	var ixFromList = inpBegRow 
	var ixToList   = ixFromList + maxNumRow
		
	var maxTo1     = ixFromList + maxNumRow; 		

	if ixToList > maxTo1        { ixToList = maxTo1; }
	if ixToList > len(inputTextRowSlice) { ixToList = len(inputTextRowSlice) }		
	var outS1 string;

	for ixRR := ixFromList; ixRR < ixToList; ixRR++  {
		rline := inputTextRowSlice[ixRR]
		//if rline.rNfile1 != 0 { continue}
		rowX := rline.rRow1	
		outS1 += "<br>;;" + strconv.Itoa( rline.rNfile1) + ";;" + strconv.Itoa( ixRR) + ";; " + cleanRow(rowX) + ";; " + rline.rTran1;  
	} 	
	
	go_exec_js_function( js_function, outS1 ); 	
			
} // end of bind_go_passToJs_rowList


//------------------
func bind_go_passToJs_rowWordList(numIdOut string, numId int, js_function string) {
	//  lista di tutte le parole di una frase	
	ixRR := numId
	if ixRR >= len(inputTextRowSlice) { ixRR = len(inputTextRowSlice) - 1 }
	
	rowX := inputTextRowSlice[ixRR]

	outS1:= numIdOut + "," + strconv.Itoa(numId) + endOfLine
	
	for w:=0; w < len(rowX.rListIxUnF); w++ {  
		ixWord := rowX.rListIxUnF[w] 
	
		xWordF := uniqueWordByFreq[ixWord] 
		
		row11 := xWordF.uWord2 + "," + strconv.Itoa(xWordF.uIxUnW) + "," + 
			strconv.Itoa(xWordF.uTotRow)  + ";" + 
			fmt.Sprint( strings.Join(xWordF.uLemmaL, wSep) ) + 
			";" + fmt.Sprint( strings.Join(xWordF.uTranL, wSep)) + 
			endOfLine 
		
		outS1 += row11; 
		
	}	

	go_exec_js_function( js_function, outS1 ); 				

} // end of bind_go_passToJs_rowWordList 

//-----------------------------------------------------------
func bind_go_write_lang_dictionary( langAndVoiceName  string) { 
		
		outFileName		:= dictionaryFolder + string(os.PathSeparator) + langFile;  		
		
		fmt.Println("bind_go_write_lang_dictionary file=" + outFileName +"\n\t",  langAndVoiceName );  	
		
		if langAndVoiceName[0:9] != "language=" {
			fmt.Println("bind_go_write_lang_dictionary() ERROR =>" +  langAndVoiceName[0:9] + "<==");  
			return 
		}	
		
		f, err := os.Create( outFileName )
		check(err)
		defer f.Close();

		_, err = f.WriteString( langAndVoiceName )
		check(err)

		f.Sync()
		
} // end of bind_go_lang_word_dictionary 	

//-----------------------------------------------------------
func bind_go_write_word_dictionary( listGoWords string) { 
		
		//fmt.Println("bind_go_write_word_dictionary ",  listGoWords  );  		
			
		currentTime := time.Now()		
		outF1 		:= dictionaryFolder + string(os.PathSeparator) + "dictL"  		
		outFileName := outF1 + currentTime.Format("20060102150405") + ".txt"
		if len(listGoWords) < 1 { return }
		if len(listGoWords) > 9 {
			if listGoWords[0:9] == "language=" { return }
		}
			
		lemmaTranStr := "__" + outFileName + "\n" + "_lemma	_traduzione"
		
		lemmaTranStr += split_ALL_word_dict_row( listGoWords )				
		
		f, err := os.Create( outFileName )
		check(err)
		defer f.Close();

		_, err = f.WriteString( lemmaTranStr );  
		check(err) 

		f.Sync()
		
		//----------------------
		
		sort_lemmaTran() ;  // 2 in write_word_dict... utilizzabili già in questo run 
		
		rewrite_wordDict_file() 
		
		
} // end of bind_go_write_word_dictionary 	

//-----------------------------------------------------------

func split_one_word_dict_row( row1 string ) (string, int, []string, []string) {

	// eg. einem;14; ein§einem§einer	
	
	lemmaLis := make( []string,0,0 )
	tranLis  := make( []string,0,0 )
	
	if row1 == "" { return "",	-1,	lemmaLis, tranLis }                           
	
	//row1:= strings.ReplaceAll( strings.ReplaceAll( row0, ....  parentesi quadre 
	
	var field = strings.Split( row1, ";");
	
	lemmaLis = strings.Split(field[2],wSep);
	tranLis  = strings.Split(field[3],wSep); 
	
	ix1, err := strconv.Atoi( field[1] )
	if err != nil { return "",	-1,	lemmaLis, tranLis }                           //error
	 
	return field[0],ix1, lemmaLis, tranLis 
		
} // end of	split_one_Word_Dict_row(	

//-------------------------------

func split_ALL_word_dict_row(  strRows string) string {
	
	// eg. einem;14 ; ein einem einer ;  a uno uno;	  ==> word ; ix : list of lemmas ; list of translations	
	
	lemmaTranStr := ""
	
	lines := strings.Split( strRows, "\n");	
	
	var ele1 lemmaTranStruct     
	
	lenIx1:= len(uniqueWordByFreq)
	
	
	//------------  solo per controllare----	
	/**
	for ix1:=0;  ix1 < 28; ix1++ {   
		fmt.Println( "ANTONIO error7 check inizio ix1=", ix1, " uniqueWordByFreq[ix1]=" , uniqueWordByFreq[ix1] )
	}
	**/	
	/***
	fmt.Println( "ANTONIO xxxxxxxxxxxxxxxxxxxxxxxxxxxx")
	for ix1:=(lenIx1-5);  ix1 < lenIx1; ix1++ {   
		fmt.Println( "ANTONIO error7 check fine   ix1=", ix1, " uniqueWordByFreq[ix1].ixUnW ="  , uniqueWordByFreq[ix1].ixUnW )
	}
	***/
	
	//-------------- fine solo per controllare-----
	
	for z:=0;  z < len(lines); z++ {   
		
		//fmt.Println("split_ALL_word_dict_row() 1 ", lines[z] )
		
		_, ix1, lemmaLis,tranLis := split_one_word_dict_row( lines[z] )
		if ix1 < 0 { continue }		
		
		if ix1 >= lenIx1 { 
			fmt.Println("error7 1 len(uniqueWordByFreq)=", len(uniqueWordByFreq), " ix1=", ix1 ,  " lines[z=", z, "]=", lines[z] )
			continue 
		}
		if uniqueWordByFreq[ix1].uIxUnW != ix1 {	
			fmt.Println("error7 2 len(uniqueWordByFreq)=", len(uniqueWordByFreq), " ix1=", ix1 ,  " lines[z=", z, "]=", lines[z] )
			continue 
		}  // error	
		
		//swUpdList[ix1] = true 
		//numUpd++  		
		ixAlfa := uniqueWordByFreq[ix1].uIxUnW_al  	
		
		len1:= len(uniqueWordByFreq[ix1].uLemmaL)
		
		//fmt.Println("\tsplit_ALL_word_dict_row() 2 ", " ix1=", ix1, " len1=", len1, ", len(lemmaLis)=", len(lemmaLis), ",     len(tranLis)=",  len(tranLis) )
		if len1 != len(lemmaLis) { 
			fmt.Println("split_ALL_word_dict_row() 1 ", lines[z] )
			for mio1:=0; mio1 < len1; mio1++ {
				fmt.Println("\tsplit_ALL_word_dict_row() 2.1 ", "  uniqueWordByFreq[ix1].uLemmaL[", mio1,"] =>" + uniqueWordByFreq[ix1].uLemmaL[mio1] + "<==")
			}   
		}   
		if len1 != len(lemmaLis) { continue }               // error 
		if len1 != len(tranLis)  { continue }               // error 
		
		
		
		for m:=0; m < len1; m++ {
			mLemm := strings.TrimSpace( lemmaLis[m] )
			mTran := strings.TrimSpace( tranLis[m] 	)	
			uniqueWordByFreq[ix1].uTranL[m]      = mTran 					
			uniqueWordByAlpha[ixAlfa].uTranL[m]  = mTran 		 
			uniqueWordByAlpha[ixAlfa].uLemmaL[m] = mLemm	
			
			lemmaTranStr += "\n" + mLemm + "|" + mTran 	
			
			//fmt.Println("\tsplit_ALL_word_dict_row() 3 ", mLemm + "|" + mTran 	)
			
			ele1.dL_lemmaCod = newCode(mLemm) 
			ele1.dL_lemma2 = mLemm 
			ele1.dL_tran  = mTran 
			if mTran != "" { 		
				dictLemmaTran = append( dictLemmaTran, ele1 ) 
			}
		}	
	} // end of z 
	
	return lemmaTranStr
	
} // end of split_ALL_word_dict_row(


//------------------------------------------
func update_words_tranWWW( newTranWordStr string) string {
	fmt.Println("GO update_words_tranWWW newTranWordStr=", newTranWordStr);

	// eg. 	seinem;17;sein§seine;essere§il suo     // word; ixUnique...;  lemmas list separati da §; translations list separ. da §]  
	if newTranWordStr == "" {return ""}
	//												listNewTranWords += "\n" + word1 + "," + ix1 + "," + wordTran ;   // new line for dictionary 
	wordTranList := strings.Split(newTranWordStr, "\n") 	
	
	var lemma1, ixS, wordTran string
	var ixAlfa int
	
	
	//thisDictList :=  make( []wDictStruct,  len(wordTranList),  len(wordTranList) )
	//var oneDict wDictStruct
	
	lenU := len( uniqueWordByFreq)  
	
	swUpdList:= make([]bool,  lenU, lenU)
	numUpd:=0
	for i:= 0; i < len(wordTranList); i++ {
		//sw := (strings.Index( wordTranList[i], "sein") >= 0 )
		//if sw {fmt.Println( "\n" + "wordTranList[",i,"]=" , wordTranList[i] ) }
		
		if wordTranList[i] == "" { continue }
		col0:= strings.Split( wordTranList[i], ";")	
		if len(col0) != 2 { continue}  
		col1:= strings.Split( col0[0], ",")
		if len(col1) != 2 { continue}  
		
		lemma1   = strings.TrimSpace( col1[0] )
		ixS      = col1[1]
		wordTran = strings.TrimSpace( col0[1] ) 
		ix1, err := strconv.Atoi(ixS)
		if err != nil { continue} 		
		
		if uniqueWordByFreq[ix1].uIxUnW != ix1 { continue } 
		
		swUpdList[ix1] = true 
		numUpd++  
		
		ixAlfa = uniqueWordByFreq[ix1].uIxUnW_al   		
		lemmaLis := uniqueWordByFreq[ix1].uLemmaL
		
		for m:=0; m < len(lemmaLis); m++ {
			if lemma1 == lemmaLis[m] {
				uniqueWordByFreq[ix1].uTranL[m]      = wordTran 					
				uniqueWordByAlpha[ixAlfa].uTranL[m]  = wordTran 
				uniqueWordByAlpha[ixAlfa].uLemmaL[m] = lemma1
				//if ix1 == 17 {  fmt.Println("\t\tm=", m, ", tran[]=", uniqueWordByFreq[ix1].uTranL[m]  ) }
				break	
			}
		}	
		
		//if ix1 == 17 {  fmt.Println( ix1, " ", swUpdList[ix1] , " uniqueWordByFreq[ix1]=",  uniqueWordByFreq[ix1] )   	}
		
	} // end of for i 
	//-------

	//fmt.Println("aggiornati ",  numUpd , " uniqueWordByFreq"  , " lenU=" , lenU)
	
	var newStr = ""
	
	for ix1:= 0; ix1 < lenU; ix1++ {
		if swUpdList[ix1] == false { continue }
		
		//  fmt.Println( "XXXXXXXXXXXXXXXX  ix1=", ix1, " ", swUpdList[ix1] , " uniqueWordByFreq[ix1]=",  uniqueWordByFreq[ix1] )   	
		  
		sU := uniqueWordByFreq[ix1]	
		lemmaLis := sU.uLemmaL
		tranLis  := sU.uTranL
		/**
		if ix1 == 17 {
			fmt.Println( " uniqueWordByFreq[ix1]=",  uniqueWordByFreq[ix1] )
			fmt.Println("\tlemmaL =",uniqueWordByFreq[ix1].uLemmaL, "\n\ttranL=",  uniqueWordByFreq[ix1].uTranL ) 
		}
		**/
		
		lemmS:= ""; tranS:=""
		for m:=0; m < len(lemmaLis); m++ {
			lemmS += "," +lemmaLis[m]
			tranS += "," +tranLis[m]
			//if ix1 == 17 {fmt.Println( " lemmS=" + lemmS, "  \t ", " tranS=", tranS) }
		}	
		lemmS += " " ; tranS += " "
		newStr += sU.uWord2 + ";" + strconv.Itoa(ix1) + ";" +
				strings.TrimSpace( lemmS[1:] ) + ";" + strings.TrimSpace(tranS[1:]) + ";" + "\n"	
		//if ix1==17 {  fmt.Println("newSTR=" , newStr) }		
	}
	//fmt.Println( "\nupdate words \n", newStr, "\n---------------------------") 
	return newStr
	
} // end of update_words_tranWWW

//-----------------------------------------------------------

func bind_go_write_row_dictionary( listGoRows string) {
		/**
		2;Primo capitolo
		4;Gustav Aschenbach o von Aschenbach, come ha fatto sin dai suoi cinquant'anni
		5;compleanno, era il suo nome ufficiale, era l'uno
		**/
		
		currentTime := time.Now()		
		outF1 		:= dictionaryFolder + string(os.PathSeparator) + "dictR"  		
		outFileName := outF1 + currentTime.Format("20060102150405") + ".txt"		
		
		numTran:= write_rowDictTranslation( strings.Split(listGoRows,"\n") )
		if numTran == 0 { return }
		
		f, err := os.Create( outFileName )
		check(err)
		defer f.Close();

		_, err = f.WriteString( listGoRows )
		check(err)
		//fmt.Printf("wrote %d bytes\n", n3)

		f.Sync()
		
		//-----------------------------------
		rewrite_rowDict_file() 
		
} // end of bind_go_write_row_dictionary 	

//--------------------

func write_rowDictTranslation( rowDictRow [] string) int {
	
	// add translated rows to the entries of inputTextRowSlice ( same index )  
	
	var len1 = len(inputTextRowSlice)
	numTran:=0
	for z:=0; z < len(rowDictRow); z++ {  
		
		/**
		2;Primo capitolo
		4;Gustav Aschenbach o von Aschenbach, come ha fatto sin dai suoi cinquant'anni
		5;compleanno, era il suo nome ufficiale, era l'uno
		**/
		row1dict := rowDictRow[z] 
		
		k1 	 := strings.Index(row1dict, ";")
		if k1 < 0 { continue; }
		ixS  := row1dict[0:k1]
		tranS := strings.TrimSpace(row1dict[k1+1:])
		ixRow, err := strconv.Atoi(  strings.TrimSpace( ixS ) )		
		if err != nil {
			return 0
		}
	
		if ixRow >= len1 { return 0 }  // error 
		inputTextRowSlice[ixRow].rTran1 = tranS
		
		//fmt.Println("\t?? anto inputTextRowSlice[ixRow] = ", inputTextRowSlice[ixRow] )
		numTran++
	}		
	return numTran
	
} // end of writeRowDictTranslation


//====================================================
func endBegin() {
	sw_begin_ended = true 	
	if sw_HTML_ready {
		bind_goStart()
	}		
}
//---------------
func begin() { 	
	
			progressivePerc(true,   6 ,"1-Begin() - start")   // 6 secs
	
	setHtmlEnv();	
	
	readTextFiles(); 
	
			progressivePerc(true,   10 ,"3-readTextFiles()" ) 
	if sw_stop { endBegin(); return }
	
	buildWordList() 	   	
	
	if sw_stop { endBegin(); return }
	
	elabWordList() 	
	
			progressivePerc(true,   97,"19-elabWordList()" ) 
	
	//sort_lemmaTran()  
	
	//		progressivePerc(true,   97 ,"20-sort_lemmaTran()" ) 
	
	if sw_rewrite_wordLemma_dict { rewrite_word_lemma_dictionary() }
	
			progressivePerc(true,   99 ,"21-rewrite_word_lemma_dictionary()" ) 
	
	if sw_rewrite_word_dict { rewrite_wordDict_file() }
	
			progressivePerc(true,   99 ,"22-rewrite_word_dict()" ) 
			
 	if sw_rewrite_row_dict {  rewrite_rowDict_file() }	
	
			progressivePerc(true,   99 ,"23-rewrite_row_dict() " )
			
	endBegin()

	progressivePerc(true,   100 ,"24-Begin() - end")  	

}// end of begin	
 	
//------------------------------------
func setHtmlEnv() {	
    // load file html 	
	
	html_path = getCompleteHtmlPath( parameter_path_html ) 
	            
	fmt.Println("path html        = " + html_path)
	
	ui.Load("file:///" + html_path + string(os.PathSeparator) + "wordsByFrequency.html" ); 
} // end of setHtmlEnv
//--------------------------------------------------------
//-------------------------
func getCompleteHtmlPath( path_html string) string {
	
	//curDir    := "D:/ANTONIO/K_L_M_N/LINGUAGGI/GO/_WORDS_BY_FREQUENCE/WbF_prova1_input_piccolo
	 
	curDir, err := os.Getwd()
    if err != nil {
		fmt.Println("setHtmlEnv() 3 err=", err)
        log.Fatal(err)
    }	
				
	fmt.Println("curDir           = " + curDir ); 
	
	curDirBack  := curDir
	k1:= strings.LastIndex(curDir, "/") 
	k2:= strings.LastIndex(curDir, "\\") 
	if k2 > k1 { k1 = k2 } 
	curDirBack = curDir[0:k1] 	
	
	var newPath string = ""
	if strings.Index(path_html,":") > 0 {
		newPath = path_html
	} else if path_html[0:2] == ".." {
		newPath = curDirBack  + path_html[2:] 
	} else {
		newPath = curDir + path_html
	}
	return newPath 
} 
//------------------------
//----------------------
func putFileError( msg1, inpFile string) {
	err1:= `document.getElementById("id_startwait").innerHTML = '<br><br> <span style="color:red;">§msg1§</span> <span style="color:blue;">§inpFile§</span>';` ; 		
	err1 = strings.ReplaceAll( err1, "§msg1§", msg1 ); 	 
	err1 = strings.ReplaceAll( err1, "§inpFile§", inpFile); 	
	ui.Eval( err1 );	
}   
//------------------

func readTextFiles() {
	//  html/js are not available when this function and others called by this run ( then ui.Eval cannot be used)   
	
	progressivePerc(true,   6 , "2-start reading text files")
	
	fileToReadList := make([]string,1,1)	
	
    readFile, err := os.Open( inputFileList )  
    if err != nil {	
		msg1:= "errore nella lettura del file " + inputFileList
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
					`<span style="color:blue;">` + inputFileList + `</span>`	+
					`<br><span style="font-size:0.7em;">(` + 	"readTextFiles()" + ")" + "</span>"
		fmt.Println(msg1)
		sw_stop = true 
		return		
    }
    fileScanner := bufio.NewScanner(readFile) 
    fileScanner.Split(bufio.ScanLines)  
	
	//toCompList :=""
	fileToReadList[0] = ""; 
	
	sw_nl_only  = false	
	//var separRow_save = separRow
	//--------	
    for fileScanner.Scan() {
        fline00:= fileScanner.Text()		
		if (fline00 == "") {continue}    // ignore zero length line 
		fline:= strings.Split(fline00, "//")[0]           // ignore all after // 
		fline = strings.Split(fline,   "/*")[0]           // ignore all after /* 
		fli  := strings.Split(fline,   "=")               //  dictionary_folder=folder of the dictionary files,   or file = filename  
		if len(fli) < 2 { continue} 
		varia1 := strings.ToLower( strings.TrimSpace(fli[0]) ) 
		value1 := strings.TrimSpace(fli[1]) 
	
		//fmt.Println("nread file list " , fline) 
		rowArrayCap   := 0	
		wordSliceCap  := 0
		uniqueWordsCap:= 0
		//-------------------
		switch varia1 {
			case "max_num_lines" :
				rowArrayCap, err = strconv.Atoi(value1)
				if err != nil { rowArrayCap = 0;}  
				if rowArrayCap > 0 {
					inputTextRowSlice    = make( []rowStruct,   0, rowArrayCap) 					
					isUsedArray          = make( []bool       , 0, rowArrayCap)  
					dictionaryRow        = make( []rDictStruct, 0, rowArrayCap)    
					fmt.Println("max_num_lines     :", rowArrayCap, " (inputTextRowSlice capacity)")  
				}
				
			case "max_num_words" : 
				wordSliceCap, err = strconv.Atoi(value1)
				if err != nil { wordSliceCap = 0;}  
				if wordSliceCap > 0 {
					wordSliceAlpha = make([]wordStruct, 0, wordSliceCap)   
					fmt.Println("max_num_words     :", wordSliceCap, " (wordSliceFreq capacity)")  
				}
				
			case "max_num_unique":
				uniqueWordsCap, err = strconv.Atoi(value1)
				if err != nil { uniqueWordsCap = 0;}  
				if uniqueWordsCap > 0 {
					uniqueWordByFreq    = make([]wordIxStruct, 0, uniqueWordsCap)  					
					dictionaryWord      = make([]wDictStruct,  0, uniqueWordsCap)  			 
					//uniqueWordByAlpha   = make([]wordIxStruct, 0, uniqueWordsCap)  
					fmt.Println("max_num_uniques   :", uniqueWordsCap, " (uniqueWordsByFreq capacity)")  
				}	
				
			case "text_split_ignore_newline" :           // if true, newLine Character (\n) are ignored and the text is split only by full stop or any of other character as .;:!?    
				value1 = strings.ToLower(value1)					
				fmt.Println("text_split_ignore_newline :", value1)  
				if value1 == "true" {   
					//??anto1 separRow = strings.ReplaceAll( separRow, "\n", "") 
					//??anto1 separRow = strings.ReplaceAll( separRow, "\r", "") 
					sw_ignore_newLine = true 
					//fmt.Println("\tsplit row chars. = " + separRow)  
				}
				
			case "text_split_by_newline_only" :   		
				value1 = strings.ToLower(value1)					
				fmt.Println("text_split_by_newline_only :", value1)  
				if value1 == "true" {  
					//??anto1 separRow = separRowFalse   // use only \n or \r
					sw_nl_only = true 
					//fmt.Println("\tsplit row chars. = " + separRow)  
				}  				
							
			case "main_text_file"  :
				fname:= strings.ReplaceAll(value1,"\\","/") 
				fileToReadList[0] = fname; //   = append(fileToReadList, fname );
				//if (toCompList == "") {	toCompList += fname;   		}	// soltanto il primo
				
			case "text_file"  :
				fname:=  strings.ReplaceAll(value1,"\\","/") 
				fileToReadList = append(fileToReadList, fname );	
				
			case "dictionary_folder"  : 
				dictionaryFolder =  strings.ReplaceAll(value1,"\\","/") 
				fmt.Println("dictionary_folder = " + value1 )
				
			case "lemma_file" : 	
				inpLemmaFile =  strings.ReplaceAll(value1,"\\","/") 	
				fmt.Println("lemma file        = " + value1 )
				
			case "lemma_file2" : 	
				inpLemmaFile2 =  strings.ReplaceAll(value1,"\\","/") 	
				fmt.Println("lemma file        = " + value1 )	
				
			case "level_file" : 	
				inpParaFile = strings.ReplaceAll(value1,"\\","/") 	
				fmt.Println("level paradigma file = " + value1 )	
			
			case "rewrite_word_lemma_dictionary" :
				sw_rewrite_wordLemma_dict = (value1 == "true") 				
			
			case "rewrite_lemma_tran_dictionary" :
				sw_rewrite_word_dict = (value1 == "true") 
				
			case "rewrite_translated_row_dictionary"  :
				sw_rewrite_row_dict = (value1 == "true") 
		}
		
    }  
    readFile.Close()
	
	if sw_ignore_newLine && sw_nl_only {	
		fmt.Println("text_split_ignore_newline = true and text_split_by_newline_only = true,  this is incompatible, both are ignored"  )      
		//separRow = separRow_save
	}
	
	
	
	if (( len(  fileToReadList ) < 1) || (fileToReadList[0] == "") ){
		errorMSG = `<br><br> <span style="color:red;">` +
					`ERROR: "mainTextFile" is missing</span>`  + 
					`<br>( add "mainTextFile" key and value in  input file list "` + inputFileList + `"` ; 			
		fmt.Println(errorMSG);		
		sw_stop = true 
		return 			
	}  
	
	fmt.Println("")
	fmt.Println("main_text_file    = ", fileToReadList[0])  
	if len(  fileToReadList ) > 1 {
		fmt.Println("text_file         = ", fileToReadList[1:])  
	}
	fmt.Println("dictionary_folder = ", dictionaryFolder )  
	fmt.Println("lemma_file        = ", inpLemmaFile )  
	if len(inpLemmaFile2) > 0 {
		fmt.Println("lemma_file2        = ", inpLemmaFile2 )  
	}
	fmt.Println("")
	
	if len(fileToReadList) == 0 { 
		errorMSG = `<br><br> <span style="color:red;">` +
					`ERROR: non c'è nessun file da leggere</span>`  + 
					`<br>file list ` +  	`<span style="color:blue;">` + inputFileList + `</span>`			
		fmt.Println(errorMSG);		
		sw_stop = true 
		return 			
	}  
	if inpLemmaFile != ""  {
		read_lemma_file(inpLemmaFile)
	}
	if inpLemmaFile2 != ""  {
		read_lemma_file(inpLemmaFile2)
	}
	//---------------
	sort.Slice(wordLemmaPair, func(i, j int) bool {
			if (wordLemmaPair[i].lWordCod != wordLemmaPair[j].lWordCod) {
				return wordLemmaPair[i].lWordCod < wordLemmaPair[j].lWordCod
			} else {
				if (wordLemmaPair[i].lWord2 != wordLemmaPair[j].lWord2) {
					return wordLemmaPair[i].lWord2 < wordLemmaPair[j].lWord2 
				} else {
					return wordLemmaPair[i].lLemma < wordLemmaPair[j].lLemma
				}
			}
		} )		 
	//----------------	
	if inpParaFile != "" {
		read_ParadigmaFile()
	}
	read_dictionary_folder( dictionaryFolder )
	if sw_stop { return }
	
	sort_lemmaTran(); // 1 in readTextFile
	
	
	//prevRunListFile = toCompList 
	
	
	//------------------------------
	showReadFile = ""
	for nFile, ff := range fileToReadList {
		
		numLines:= read_one_inputFileText( ff , nFile);
		if numLines < 0 { sw_stop=true; return; }
		
		showReadFile = showReadFile + strconv.Itoa(numLines) + "<file>" + ff + ";" ; 
	}
	// go_exec_js_function("js_go_showReadFile", showReadFile);  
	
	fmt.Println("\ntotal number of text lines = ", numberOfRows); 
	
	
} // end of readTextFile 
	
//-----------------------------------

func buildWordList() {
    /*
	write a line in wordSliceFreq and wordSliceAlpha  for each word in the row 
	*/
	
	if  len(inputTextRowSlice) < 1 { return }  
	
	var wS1 wordStruct;
	//numMio:=0
	
	//fmt.Println("separWord=" + separWord); 

	//fmt.Println("build2_1");
	
	progressivePerc(true,   10 , "4-buildWordList" )
	
	numberOfWords=0; 
	nn:=0
	
	/***
	ever0 := float64(0.032051) * float64(  len(inputTextRowSlice) )
	every:= int( ever0 )	
	
	fmt.Println("EVERY ", every , "lines increase 1% time")
	***/
	lastPerc = 10;
	
	//----
	delta1 := (37.0- float64(lastPerc) ) / float64( len( inputTextRowSlice) )  
	percX1 := float64( lastPerc )  
	//fmt.Println("delta1=", delta1)
	//---------------------
	for ixR, rS2 := range inputTextRowSlice {	//  for each text row 
		row2   := rS2.rRow1;		
		if sw_HTML_ready {
			percX1 += delta1 
			if ixR == (1000 * int(ixR/1000)) {
				//fmt.Println("ixR=", ixR, " percX1=", int( percX1 ) )
				go_exec_js_function( "showProgress", strconv.Itoa( int( percX1 ) ) ) 	
			}
		}		
		wordA  := regexp.MustCompile(separWord).Split(row2, -1);  // split row into words 
        z:= -1;
		for _, wor1 := range wordA {
			wS1.wWord2 = strings.ToLower(strings.TrimSpace(wor1));
			if wS1.wWord2 == "" || isThereNumber( wS1.wWord2 ) || wS1.wWord2 == "%" ||  wS1.wWord2 == "&amp" { 			
				continue;
			}	
			if wS1.wWord2[0:1] < " "  {
				continue
			}	
			z++;
			nn++
			wS1.wNfile    = rS2.rNfile1 
			wS1.wIxRow    = ixR   // index of row containing the word 
			wS1.wIxPosRow = z;    // position of the word in the row 
			wordSliceAlpha = append(wordSliceAlpha, wS1);
			
		}
	} // end of for_ixR 
	
	//---------------------------------------
	numberOfWords = len(wordSliceAlpha); 

	fmt.Println("ANTONIO3  numberOfWords=", numberOfWords)
	
	progressivePerc(true,  37, "5-extracted " + strconv.Itoa(numberOfWords) + "words from text" ) // 26 secs  4 milioni
		
	fmt.Println("number of words in text lines ", numberOfWords);
	
	//----	
	sort.Slice(wordSliceAlpha, func(i, j int) bool {
		return wordSliceAlpha[i].wWord2 < wordSliceAlpha[j].wWord2            // word  ascending order (eg.   a before b ) 		
	})
	//------------------------------
	addCodedWordToWordSlice()
	//---------------------------------
	
	// now wordSliceAlpha is in order by coded word and actual word ( eg. both actual word "über"   and "ueber" have "uber" as coded word) 
	
	/**
	for g:=0; g < len( wordSliceAlpha ); g++ {
		if g > 20 {fmt.Println("ANTONIO2 alpha ", "... continua");  break;  }
		fmt.Println( "ANTONIO2 alpha ", wordSliceAlpha[g] )
	}	
	**/
	
	
	progressivePerc(true,  55 ,"6-words sorted")  // 18 secs
	
} // end of buildWordList
//-----------------
func addCodedWordToWordSlice() {
	/*
	add a sortKeyWord to each word element
	*/
	preW     := "" 	
	preCoded := ""
	//----------------
	for i, wS1 := range wordSliceAlpha {
		if (wS1.wWord2 != preW) { 
			preW = wS1.wWord2	
			preCoded = newCode(preW)
		}
		wordSliceAlpha[i].wWordCod = preCoded;
	}	
	//----	
	sort.Slice(wordSliceAlpha, func(i, j int) bool {
		if wordSliceAlpha[i].wWordCod != wordSliceAlpha[j].wWordCod {
			return wordSliceAlpha[i].wWordCod < wordSliceAlpha[j].wWordCod            // word  ascending order (eg.   a before b ) 
		} else {
			if wordSliceAlpha[i].wWord2 != wordSliceAlpha[j].wWord2 {
				return wordSliceAlpha[i].wWord2 < wordSliceAlpha[j].wWord2  
			} else {
				return wordSliceAlpha[i].wNfile < wordSliceAlpha[j].wNfile          // nFile ascending order (eg.   0 before 1 ) 
			}
		}
	})
	//------------------------------
	
	
} // end of addCodedWordToWordSlice

//------------------------------------------------

func elabWordList() {
	
	
	addTotRowToWord()	
	
		progressivePerc(true,  56 , "7-elab.words 2 finito addRowToWord")
		
	elabWordAlpha_buildWordFreqList() 		
	
		progressivePerc(true,  73 , "8-elab.words 3 finito elabWordAlpha_buildWordFreqList" )  // 17 secs
		
	build_uniqueWord_byFreqAlpha(); 
	
	putWordFrequenceInRowArray()

	addRowTranslation() 
	
		progressivePerc(true,  96 , "17-elab.words 4 finito addRowTranslation() " )
	
	build_lemma_word_ix()
		progressivePerc(true,  97 , "18-elab.words 4 finito add_lemma_word_ix, finito elabWordList" )
	
	
} // end of elabWordList()

//----------------------------------------------

func addTotRowToWord() {
	/*
	each element of wordSliceAlpha contains a word (the same word may be in several rows) 
	the number of repetition of a word (totRow) is put in its element  ( later will be put in each row that contain it) 
		eg.  one 3, one 3, one 3, two 4, two 4, two 4, two 4	
	*/
	preW  := wordSliceAlpha[0].wWordCod;	
	totR  := 0	
	ix1   := 0
	ix2   :=-1
	//----------------
	for i, wS1 := range wordSliceAlpha {
		
		//fmt.Println("ANTO addTot ... i=" , i , " => ", wS1 )
		
		if (wS1.wWordCod != preW) {
			ix2 = i; 
			for i2 := ix1; i2 < ix2;i2++ {
				 wordSliceAlpha[i2].wTotRow = totR;   // se una parola è ripetuta 3 volte, ad ogni parola è associato 3  
			}			
			
			totR = 0
			ix1  = i; 
			preW = wS1.wWordCod; 
		} 
		totR++;     	
	}
	ix2++; 
	for i2 := ix1; i2 < len(wordSliceAlpha);i2++ {
		wordSliceAlpha[i2].wTotRow = totR; 
	}
	
	
	
	//------
	
	
} // end of addTotRowToWord 

//---------------------------------

func elabWordAlpha_buildWordFreqList() {
	/*
	put in each row of the inputTextRowSlice the number of its words  
	from wordSliceAlpha list obtain a new list by sorting it by occurrence of the words (totRow) 
	*/
	//preW  := ""; // wordSliceAlpha[0].word;	
	//ix:=0;
	//removeIxWord :=-1 
	
	
	//progressivePerc(true,  56 , "7.1-elabWordAlpha_buildWordFreqList")	
	
	/******************** rimosso il 15/11/2023
	
	for nn, wS1 := range wordSliceAlpha {	
		if wS1.wWordCod == LAST_WORD  { wordSliceAlpha[nn].totRow = LAST_WORD_FREQ }
		//fmt.Println("ANTO elab...FreqList() ", nn, "  alpha=",  wordSliceAlpha[nn]);  	
		//fmt.Println("ANTO elab...FreqList() nn=", nn, ", preW=" + preW + ",  wS1 ", wS1)  
		
		if (wS1.wWordCod != preW) {		
			removeIxWord = -1
			preW = wS1.wWord2; 
			if wS1.nFile > 0 { removeIxWord = nn}   // dal secondo file in poi (il primo file ha indice 0) 	
		}
		ix =  wS1.ixRow
		inputTextRowSlice[ix].numWords ++; 		// how many words contains the row (eg. the row "the cat is on the table"  contains 6 words --> .numWords = 6 
		if removeIxWord >= 0 {
			//fmt.Println("\t ANTO 2elab" , "  removeIxWord=" , removeIxWord , " wordSliceAlpha[ removeIxWord ].word=" + wordSliceAlpha[ removeIxWord ].word  )
			
		    if wS1.wWordCod == wordSliceAlpha[ removeIxWord ].wWordCod {
				wordSliceAlpha[ nn ].sw_ignore = true 
			}	
		}	
		//fmt.Println("\t ANTO XXXelab"  , "  wS1.sw_ignore = ", wS1.sw_ignore)  
	}
	*****************************/
	
	//----------------
	for nn, wS1 := range wordSliceAlpha {	
		if wS1.wWordCod == LAST_WORD  { wordSliceAlpha[nn].wTotRow = LAST_WORD_FREQ }	
		inputTextRowSlice[ wS1.wIxRow ].rNumWords ++; 		// number of words in a row (eg. the row "the cat is on the table"  contains 6 words --> .numWords = 6 
	}
	//------------
	//progressivePerc(true,  56 , "7.2-elabWordAlpha_buildWordFreqList")	
	//------------
	// build WordList by frequence in the text
	// the slice is sorted in descending order of frequency   ( ie. firstly the most used)   
	//-----------------------------------
	
	wordSliceFreq  = make([]wordStruct, len(wordSliceAlpha),  len(wordSliceAlpha) ) 	 // la slice destinazione del 'copy' deve avere la stessa lunghezza di quella input  
	
	copy(wordSliceFreq , wordSliceAlpha);
	
	//progressivePerc(true,  56 , "7.3-elabWordAlpha_buildWordFreqList")	
	
	// le parole eguali si trovano in righe contigue perchè hanno la stessa frequenza
	
	sort.Slice(wordSliceFreq, func(i, j int) bool {
			if wordSliceFreq[i].wTotRow !=  wordSliceFreq[j].wTotRow {
			   return wordSliceFreq[i].wTotRow > wordSliceFreq[j].wTotRow        // totRow    descending order (how many row contain the word) 
			} else {
				if wordSliceFreq[i].wWordCod != wordSliceFreq[j].wWordCod {
					return wordSliceFreq[i].wWordCod < wordSliceFreq[j].wWordCod            // word  ascending order (eg.   a before b ) 
				} else {
					return wordSliceFreq[i].wWord2 < wordSliceFreq[j].wWord2  			
				}
			}
		})
	progressivePerc(true,  56 , "7.4-elabWordAlpha_buildWordFreqList")	
	
	
} // end of elabWordAlpha_buildWordFreqList

//--------------------------------------

func putWordFrequenceInRowArray() {

	ix:=0;

	//-------------------------	
	//  in each element of inputTextRowSlice define an empty slice to contain the frequence of each of its words
	for k, _ := range inputTextRowSlice {	
		tot1 := inputTextRowSlice[k].rNumWords;
		inputTextRowSlice[k].rListIxUnF =  make( []int, tot1, tot1 )		
		inputTextRowSlice[k].rListFreq  =  make( []int, tot1, tot1 )			
	}
	
	//---------------------------------
	//  fill each row with the frequence of its words
	//-------------------	
	
	for _, wS1 := range wordSliceFreq {	
		//fmt.Println("ANTO putWordFrequenceInRowArray() wS1 ", wS1)  
		
		ix = wS1.wIxRow; 
		ixPos := wS1.wIxPosRow; 
		/****
		num2 := len(inputTextRowSlice[ix].rListFreq) 
		if (num2 <= ixPos) {		
			fmt.Println("error " , wS1.wWord2, " ix=" , ix  ," ixPos=",   ixPos, " row ", " num2=", num2, " tot1=",  
				inputTextRowSlice[ix].rNumWords, " list=" , inputTextRowSlice[ix].rListFreq , " " , inputTextRowSlice[ix].rRow1); 			
		}
		if ((ixPos<1) || (ix<1)) {
			fmt.Println( "ERRORe  putWordFrequenceInRowArray() nx=", nx, " WS1=", wS1, "\n\t", "ix=", ix, ", ixPos=", ixPos)  
		}
		***/
		inputTextRowSlice[ix].rListIxUnF[ixPos] = wS1.wIxUniq // index of the word in the uniqueWordByFreq  	
		inputTextRowSlice[ix].rListFreq[ ixPos] = wS1.wTotRow // for each word in the row  set its frequence of use (how many times the word is used in the whole text)  	
	}
	
	//---------------------------
} // end of putWordFrequenceInRowArray

//------------------------------------------------

func put_a_priority_to_the_row_of_each_word() {
		
	//the row importance is assigned by the number of its unknown words	
	
	progressivePerc(true,  73 , "10-put a priority"  )
	
	for k, wS1 := range wordSliceFreq {	
		
		ix := wS1.wIxRow; 
		numMinor :=0 	
		wordFreq := wS1.wTotRow; 		
		for _, frw:= range   inputTextRowSlice[ix].rListFreq {
			if frw < wordFreq { numMinor++; }
		} 
		wordSliceFreq[k].wTotMinRow = numMinor;	             // number of words with frequency < this word   	
		wordSliceFreq[k].wTotWrdRow = inputTextRowSlice[ix].rNumWords   // number of words in this row    
	}		
	
	progressivePerc(true,  75 , "11-put a priority sort" ) 
	
	sortWordListByFreq_and_row_priority() 
		
} // end of put_a_priority

//--------------------------------------
func build_uniqueWord_byFreqAlpha() {

	progressivePerc(true,  73, "9-build_uniqueWord_add_frequence 1")
	
	put_a_priority_to_the_row_of_each_word() 	
		
	preW := ""
	numWordUn := 0
	numWordRi := 0	
	num_word:=0
	
	numWordUn_0 := 0
	numWordRi_0 := 0	
	num_word_0 :=0 
	//--------------------
	
	progressivePerc(true,  86 , "12-build_uniqueWord_add_frequence 2" )  // 12 secs
	
	for _, wS1 := range wordSliceFreq {	
		num_word++
		//if wS1.sw_ignore == false { 
		num_word_0++
		//}
		
		if wS1.wWordCod != preW {
			preW = wS1.wWordCod;
			numWordUn += 1 
			numWordRi += wS1.wTotRow 
			//if wS1.sw_ignore == false { 
			numWordUn_0 += 1 
			numWordRi_0 += wS1.wTotRow 
			//}
		}  
	}
	progressivePerc(true,  87 , "13-build_uniqueWord_add_frequence 3" )
	//------------
	if num_word_0 != num_word {
		fmt.Println( "PAROLE SINGOLE File0= ", numWordUn_0, ", PAROLE Totale=", numWordRi_0,  "  numberOfWords=" , num_word_0 , " "  );
	}
	fmt.Println( "PAROLE SINGOLE tutti= ", numWordUn, ", PAROLE Totale=", numWordRi,  "  numberOfWords=" , num_word , "\n");
	
	progressivePerc(true,  87 ,  "14-build_uniqueWord_add_frequence 4" )
	//--
	//numberOfUniqueWords = numWordUn;
	numberOfUniqueWords = numWordUn_0;
	preW      = ""
	numWordUn = 0
	numWordRi = 0	
	
	percIx := 0; 	

	//result_word2 ="";
	
	var xWordF wordIxStruct;   
	var sS  statStruct;
	
	//numWordUn = -1
	numWordUn = 0
	
	//-----------------------------
	/**** removed 2023_11_15
	// remove elements to ignore  ( those of the files after the first )
	wrk := wordSliceFreq[:0]
	for _, wS1 := range wordSliceFreq {				
			if wS1.sw_ignore { continue }
			wrk = append( wrk, wS1) 
	}
	wordSliceFreq = wrk		
	**/
	//--------------------
	/**
	for n0, wS1 := range wordSliceFreq {	
		if n0 > 20 {fmt.Println("ANTONIO1 build_uniqueWord_byFreqAlpha() ", "... continua");  break;  }
		fmt.Println("ANTONIO1 build_uniqueWord_byFreqAlpha() ", wS1) 
	}
	***/
	//---------
	for n1, wS1 := range wordSliceFreq {	
		if wS1.wWordCod != preW {
			preW = wS1.wWordCod;
			if wS1.wTotRow >= LAST_WORD_FREQ {
				wS1.wTotRow = 0
			}
			xWordF.uWordCod = wS1.wWordCod;
			xWordF.uWord2   = wS1.wWord2;
			xWordF.uTotRow   = wS1.wTotRow
			xWordF.uIxWordFreq = n1
			//xWordF.wTran = "" 
			xWordF.uIxUnW     = len(uniqueWordByFreq)  
			uniqueWordByFreq = append( uniqueWordByFreq, xWordF);  
			numWordUn += 1 
						
			numWordRi += wS1.wTotRow 
			percIx = int(numWordUn * 100 / numberOfUniqueWords); 
			//if percIx < 2 { fmt.Println( percIx, "% parole,  n1=" , n1 , " (ultima=" , xWordF.word, " numWordUn=" , numWordUn, " freq=" , xWordF.totRow, " ", numWordUn * 100 / numberOfUniqueWords, "%"   )}
			
			sS.uniqueWords = numWordUn 
			sS.totWords    = numWordRi
			sS.uniquePerc  = percIx 
			sS.totPerc     = int(numWordRi * 100 / numberOfWords);
			
			//if sS.totPerc > 100 {  fmt.Println("AN TONIO4 n1=", n1, " len(wordSliceFreq)=",  len(wordSliceFreq) , " wS1.wWord2=" + wS1.wWord2 + " wS1.totRow=", wS1.totRow, " numWordRi=", numWordRi ) }
			
			/**
			if strconv.Itoa(1000 + percIx)[3:] == "0" {  
				wordStatistic_un[percIx] = sS; 	
			}
			***/				
			if sS.totPerc <= 200 {   // esistono perc > 100%,  probabilmente c'è un errore di logica 
				if strconv.Itoa(1000 + sS.totPerc)[3:] == "0" {				
					wordStatistic_tx[sS.totPerc] = sS; 
				}
			}
			//fmt.Println("STAT. ", n1, " ", xWordF.word, " numWordUn=", numWordUn,  " numWordRi=", numWordRi, " percIx=", percIx, " ", sS.uniquePerc,  " sS.totPerc=" ,  sS.totPerc); 
		} 			
	}
	//---------
	
	highestValueByte, err := hex.DecodeString("ffff")   
	if err != nil { panic(err) }
	var highestValue = string( highestValueByte ) + "end_of_list"	
	xWordF.uWordCod = highestValue 
	xWordF.uWord2   = highestValue 	
	
	xWordF.uTotRow = 1 ; // the lowest frequency
	xWordF.uIxWordFreq = len(uniqueWordByFreq)   
	xWordF.uIxUnW      = len(uniqueWordByFreq)  
	xWordF.uTranL      = []string{ xWordF.uWord2 }   
	uniqueWordByFreq   = append( uniqueWordByFreq, xWordF);  
	
	//--------------------------
	
	progressivePerc(true,  89, "15-add lemma" )	
		
	addWordLemmaTranLevelParadigma()   
	
	add_ixWord_to_WordSliceFreq()
	
	progressivePerc(true,   91 , "16-add translation")
	
	//addWordTranslation()		
	
	//---------------------
	uniqueWordByAlpha = make([]wordIxStruct, len(uniqueWordByFreq),  len(uniqueWordByFreq))	 // la slice destinazione del 'copy' deve avere la stessa lunghezza di quella input  
	
	stat_useWord();
	
	copy( uniqueWordByAlpha, uniqueWordByFreq); 
	
	
	//fmt.Println("build_uniqueWord_byFreqAlpha() PROVA len unique Freq() = ", len(uniqueWordByFreq)   )
	
	//------------
	sort.Slice(uniqueWordByAlpha, func(i, j int) bool {
		if uniqueWordByAlpha[i].uWordCod != uniqueWordByAlpha[j].uWordCod {
			return uniqueWordByAlpha[i].uWordCod < uniqueWordByAlpha[j].uWordCod            // word  ascending order (eg.   a before b ) 
		} else {
			return uniqueWordByAlpha[i].uWord2 < uniqueWordByAlpha[j].uWord2  			
		}
	})
	//---------

	//console( "\nlista uniqueWordByAlpha")	
	// update alpha index  // ixUnW,  ixUnW_al	
	
	fmt.Println("build_uniqueWord_byFreqAlpha() PROVA len unique alpha() = ", len(uniqueWordByAlpha)   )
	
	for u:=0; u < len(uniqueWordByAlpha); u++ {
		f:= uniqueWordByAlpha[u].uIxUnW
		uniqueWordByFreq[f].uIxUnW_al  = u; 		
		uniqueWordByAlpha[u].uIxUnW_al = u
		/**
		if u > 5120 {  			
			 fmt.Println( "uniqueWordByAlpha ANTONIO prova u=", u , " \t unique = ", uniqueWordByAlpha[u].uWordCod , " \t ",   uniqueWordByAlpha[u].uWord2) 
		}
		**/		
	}
 	//console( "------------------\n")
	
	fmt.Println("\n---------------- build_uniqueWord_byFreqAlpha() end  \n")
	

} // end of build_uniqueWord_byFreqAlpha

//-----------------------
func build_lemma_word_ix() {
	
	//	build a slice with all lemma with all words 
	/*
	lemmaWordStruct struct {lw_lemmaCod string, lw_lemma2 string, lw_word  string, lw_ix int
	*/
	lemma_word_ix = make([]lemmaWordStruct, 0, 0)  
	
	var wL lemmaWordStruct
	
	for z:=0; z < len(uniqueWordByFreq); z++ {		 	
		wL.lw_word = uniqueWordByFreq[z].uWord2 
		wL.lw_ix   = uniqueWordByFreq[z].uIxUnW
		
		lemmaLis :=  uniqueWordByFreq[z].uLemmaL
		
		for m:=0; m <  len(lemmaLis); m++ {
			wL.lw_lemma2   = lemmaLis[m]   
			wL.lw_lemmaCod = newCode( wL.lw_lemma2 )    
			lemma_word_ix = append( lemma_word_ix, wL )
		}	
	} 
	//--------------
	// order by lemma and word 	
	sort.Slice(lemma_word_ix, func(i, j int) bool {
			if  lemma_word_ix[i].lw_lemmaCod != lemma_word_ix[j].lw_lemmaCod {
				return lemma_word_ix[i].lw_lemmaCod < lemma_word_ix[j].lw_lemmaCod 	
			} else {
				if  lemma_word_ix[i].lw_lemma2 != lemma_word_ix[j].lw_lemma2 {
					return lemma_word_ix[i].lw_lemma2 < lemma_word_ix[j].lw_lemma2	
				} else {
					return lemma_word_ix[i].lw_word < lemma_word_ix[j].lw_word 
				}				
			}
		} )		
	 
} // end of build_lemma_word_ix  
 

//--------------------------

func sortWordListByFreq_and_row_priority() {

	sort.Slice(wordSliceFreq, func(i, j int) bool {
		if wordSliceFreq[i].wTotRow !=  wordSliceFreq[j].wTotRow {
		   return wordSliceFreq[i].wTotRow > wordSliceFreq[j].wTotRow        // totRow    descending order (how many row contain the word) 
		}
		if wordSliceFreq[i].wWordCod !=  wordSliceFreq[j].wWordCod {
		   return wordSliceFreq[i].wWordCod < wordSliceFreq[j].wWordCod            // word      ascending order	  		   
		}	
		if wordSliceFreq[i].wWord2 !=  wordSliceFreq[j].wWord2 {
		   return wordSliceFreq[i].wWord2 < wordSliceFreq[j].wWord2                // word      ascending order	  		   
		}	
		/***rimosso 15/11/2023
		if wordSliceFreq[i].nFile !=  wordSliceFreq[j].nFile {
		   return wordSliceFreq[i].nFile < wordSliceFreq[j].nFile          // nFile     ascending order  ( firstly	file 0)   		   
		}	
		***/		
		if wordSliceFreq[i].wTotMinRow !=  wordSliceFreq[j].wTotMinRow {
		   return wordSliceFreq[i].wTotMinRow < wordSliceFreq[j].wTotMinRow  // totMinRow ascending order	(how many words in the row are not yet learned) 
		}
		return wordSliceFreq[i].wIxRow < wordSliceFreq[j].wIxRow             // ixRow     ascending order	( first the rows which were first in the text)  		   
			
	})	
} // end of sortWordListByFreq_and_row_priority

//-----------------------------
/**
func print_rowArray( where string) {
		
	//result_row1 = ""; 
	
	for i, wR1 := range inputTextRowSlice {	
		if i > 10 {break;} 
		**
		strFreqList := arrayToString(wR1.listFreq, ",")
		
		strrow:= "ix="  + strconv.Itoa(i) + " w="   + strconv.Itoa(wR1.numWords) + 						
						" lf=" + strFreqList +
						" " + wR1.row1;
		**				
		fmt.Println( where , "  ",  wR1.row1);
		//result_row1 = result_row1 + "<br>" + strrow; 
	}

} // end of print_rowArray
**/

//----------------------------------------------------------------

func go_exec_js_function(js_function string, inpstr string ) {
	/*
	This function executes a javascript eval command 
	which must execute a function by passing string constant to it. 
	Should this string contain some new line, e syntax error would occur in eval the statement.
	
	To avoid this kind of error, the string argument (inpstr) of the javascript function (js_function) 
	is forced to be always enclosed in back ticks trasforming it in "template literal".  
	Just in case back ticks and dollars are in the string, they are replaced by their html symbols.   	
	*/
	inpstr = strings.ReplaceAll( inpstr, "`", " "   ); 	  
	//inpstr = strings.ReplaceAll( inpstr, "`", "&#96;"   ); 	 
	inpstr = strings.ReplaceAll( inpstr, "$", "&dollar;"); 
	
	evalStr := fmt.Sprintf( "%s(`%s`);",  js_function,  inpstr ) ; 
	
	ui.Eval(evalStr)
	
} // end of go_exec_js_function

//--------------------------------

func arrayToString(a []int, delim string) string {
    return strings.Trim(strings.Replace(fmt.Sprint(a), " ", delim, -1), "[]")
    //return strings.Trim(strings.Join(strings.Split(fmt.Sprint(a), " "), delim), "[]")
    //return strings.Trim(strings.Join(strings.Fields(fmt.Sprint(a)), delim), "[]")
}
//----------------------------

func isThereNumber(s string) bool {
    for _, c := range s {
        if c >= '0' && c <= '9' {
            return true
        }
    }
    return false
}

//------------------------------
func buildStatistics() {		
		//var rows []string
		var result string = ""
		
		if len( only_level_numWords ) < 1 { return }
		
		/***	
		msgLevelStat = "" 		
		if percA0 > 0 {msgLevelStat += ", A0: " + strconv.Itoa(percA0) + "%" }
		if percA1 > 0 {msgLevelStat += ", A1: " + strconv.Itoa(percA1) + "%" }
		if percA2 > 0 {msgLevelStat += ", A2: " + strconv.Itoa(percA2) + "%" }
		if percB1 > 0 {msgLevelStat += ", B1: " + strconv.Itoa(percB1) + "%" }
		if percOth > 0 {msgLevelStat += ", Oth: " + strconv.Itoa(percOth) + "%" }
		if len(msgLevelStat) > 1 {msgLevelStat = msgLevelStat[2:] } 
		**/
		
		msgLevelStat = "" 
		for f:=1; f < len( only_level_numWords ) ; f++ {
			if only_level_numWords[f] == 0 { continue }
			msgLevelStat += ", " + list_level[f] + ": " + strconv.Itoa( perc_level[f] ) + "%"  
		}	
		if only_level_numWords[0] > 0 {  
			msgLevelStat += ", " + list_level[0] + ": " + strconv.Itoa( perc_level[0] ) + "%"  
		}
		if len(msgLevelStat) > 1 {msgLevelStat = msgLevelStat[2:] } 

		result += "livello " + msgLevelStat //  + "..endLevel ";  
		
		for _, sS:= range wordStatistic_tx {	
			if sS.totWords == 0 { continue; }
			if sS.uniqueWords < 100 { continue}
			//fmt.Println( sS.uniqueWords , " words (",  sS.uniquePerc, "%), found ", 
			//	sS.totWords,  " times in the text(", sS.totPerc,"%)" ) 
			result += "<br>" + fmt.Sprintln( sS.uniqueWords , " words (",  
				sS.uniquePerc, "%), make up ", sS.totPerc,"% of the text (", sS.totWords, " words)") 
		}  		
		result += "<br>" 
		go_exec_js_function("js_go_updateStatistics", result )		
	
}	
//-----------------------------------
func stat_useWord() {
	len1:=  len(uniqueWordByFreq)
	len2:= float64(len1)/100
	
	fmt.Println("len1=", len1, " ", len2) 	

	lisPerc := [29]float64{0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9,1,2,3,4,5,6,7,8,9, 10,20,30,40,50,60,70,80,90,100}
	listIxPerc:= make([]int,0,40)
	for z:=0; z < len(lisPerc); z++ {
		per1 := lisPerc[z]
		per2 := int( float64(per1) * len2)
		listIxPerc = append( listIxPerc, per2 )
		//fmt.Println("stats ", per1, "% = num.Elem.",  per2 )  	
	}   
	
	lastTot:=0;
	ixNow:=0	
	for z:=0; z < len(listIxPerc); z++ {
		//from1 = ixNow
		ixNow =  listIxPerc[z]-1
		if ixNow< 0 { ixNow=0;}
		
		if uniqueWordByFreq[ixNow].uTotRow == lastTot { continue }
		
		//fmt.Println("stats ", lisPerc[z], "% = num.Elem.",  listIxPerc[z], " toIx=", ixNow,   
		//					" num.Rows per word=",uniqueWordByFreq[ixNow].totRow )
		if listIxPerc[z] >= 1 {
			fmt.Println("stats ", lisPerc[z], "% = num.Elem.",  listIxPerc[z], " sono usate   " , 
				uniqueWordByFreq[ixNow].uTotRow , " o più volte" , 
				" (", (100 - lisPerc[z]) ,  "% delle parole non sono usate più di ",  uniqueWordByFreq[ixNow].uTotRow ," volte)" )
		}
		lastTot = uniqueWordByFreq[ixNow].uTotRow 	
	} 
	
} // end of stat_useWord

//------------------------------------

func cleanRow(row0 string) string{

		row1 := strings.ReplaceAll( row0, "<br>", " "   ); 	// remove <br> because it's needed to split the lines to transmit  

		// if the row begins with a number remove this number
		row1 = strings.Trim(row1," \t")    // trim space and tab code
		k:=    strings.IndexAny(row1, " \t");	
		if (k <1) { return row1;}
		numS := row1[:k]	
		_, err := strconv.Atoi(numS)
		if err != nil { return row1;}  
		return strings.Trim(row1[k+1:]," \t"); 
}


//==============================================

func TOGLIsearchOneWordInAlphaList(  wordToFind string) (int, int) {
	
	// get the index of a word in dictionary (-1 if not found)  
	
	return searchAllWordWithPrefixInAlphaList(  wordToFind ) 	
	
	//return fromIx; 	
	
} // end of TOGLIsearchOneWordInAlphaList

//-----------------------------
func searchAllWordWithPrefixInAlphaList(  wordPref string) (int, int) {
	
	// get the indicies of the first and the last word beginning with the required prefix (-1,-1 if not found)  
	
	wordPref = strings.ToLower(strings.TrimSpace( wordPref));  
	wordCodPref:= newCode(wordPref)
	
	lenPref:= len(wordPref); 
	ixTo := -1; ixFrom:= -1;	
	
	if lenPref == 0 { return ixFrom, ixTo }
	
	ix1, ix2:= lookForWordInUniqueAlpha(wordCodPref)	
	
	/***
	fmt.Println("ANTONIO SEARCH ALPHA wordPref=" + wordPref + " wordCodPref=" +  wordCodPref + " ix1=", ix1, " ix2=", ix2) 
	for k:= ix1; k <= ix2; k++ {
		if k < 0 { continue}
		fmt.Println("ANTONIO SEARCH ALPHA k=", k , " ==>" , uniqueWordByAlpha[k])
	}	
	***/
	
	wA :=""
	spaceFill := "                                                          ";  
	//-----------
	for k:= ix1; k >= 0; k-- {
		wA =  uniqueWordByAlpha[k].uWordCod + spaceFill
		if wA[0:lenPref] < wordCodPref { break; }
		ixFrom = k; 
	}  
	
	if (ixFrom >=0) { ixTo = ixFrom; }  //  se ixFrom è valido, deve essere valido anche ixTo   
	
	for k:= ix2; k < numberOfUniqueWords; k++ {
		wA =  uniqueWordByAlpha[k].uWordCod + spaceFill  
		if wA[0:lenPref] > wordCodPref { break; }
		ixTo = k; 
		if (ixFrom < 0) {ixFrom = ixTo;}  //  se ixTo è valido, deve essere valido anche ixFrom   
	}  
	return ixFrom, ixTo 
	
} // end of searchAllWordWithPrefixInAlphaList

//--------------
func lookForWordInUniqueAlpha(wordCoded string) (int, int) {
	
	// find 2 indices of the 2 words nearest to the word to find 	
	
	low   := 0
	high  := numberOfUniqueWords - 1	
	maxIx := high; 
	//----
	for low <= high{
		median := (low + high) / 2
		if median >= len(uniqueWordByAlpha) {
			fmt.Println("errore in lookForWordInUniqueAlpha: median=", median , "     len(uniqueWordByAlpha)=" ,  len(uniqueWordByAlpha) )
		}
		if uniqueWordByAlpha[median].uWordCod < wordCoded {
			low = median + 1
		}else{
			high = median - 1
		}
	} 
	//---
	fromIx:= low; toIx := high; 
	if fromIx > toIx { fromIx = high; toIx = low;}
	if fromIx < 0 { fromIx=0} 
	if toIx  > maxIx { toIx = maxIx}
	return fromIx, toIx	

} // end of lookForWordInUniqueAlpha



//-----------------------------

func lookForLemmaWord(lemmaCode string) (int, int) {
	
	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := len(lemma_word_ix) - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if lemma_word_ix[median].lw_lemmaCod < lemmaCode {  
			low = median + 1
		}else{
			high = median - 1
		}
	} 
	//---
	fromIx:= low; toIx := high; 
	if fromIx > toIx { fromIx = high; toIx = low;}
	if fromIx < 0 { fromIx=0} 
	if toIx  > maxIx { toIx = maxIx}
	return fromIx, toIx	

} // end of lookForLemmaWord
//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

/**
//------------------------------------------------------
func testPreciseWord(target string ) {
	fmt.Println( "cerca ", target);
	var xWordF wordIxStruct;  
	ix1, ix2 := searchOneWordInAlphaList( target ) 
	
	if (ix2 < 0) {
		fmt.Println( target, "\t NOT FOUND "); 
	} else {
		for ix:= ix1; ix <= ix2; ix++ {
			xWordF =  uniqueWordByAlpha[ix] 
			fmt.Println( target, "\t found  ",  xWordF.uWord2, " ix=", ix,   " totRow=", xWordF.uTotRow,
				" ixwordFre=", xWordF.uIxWordFreq); 
		}
	} 
	fmt.Println( "-------------------------------------------------\n" ); 
} 
***/
//------------------------------------------------------
func testGenericWord(pref string ) {
	//fmt.Println( "cerca tutte le parole che iniziano con " + pref);	
	var xWordF wordIxStruct;  
	
	from1, to1 := searchAllWordWithPrefixInAlphaList( pref )
	if (to1 < 0) {
		fmt.Println( "nessuna parola che inizia con " , pref); 
	} else {	
		for i:=from1; i <=to1; i++ {	
			xWordF =  uniqueWordByAlpha[i] 
			fmt.Println( "trovato ", xWordF.uWord2, " ix=", i,   " totRow=", xWordF.uTotRow, " ixwordFre=", xWordF.uIxWordFreq); 
		}
	}
	fmt.Println( "-------------------------------------------------\n" ); 
	return 
}
//---------------------
func getScreenXY() (int, int) {
	
	// use ==>  var x, y int = getScreenXY();
	
	var width  int = int(win.GetSystemMetrics(win.SM_CXSCREEN));
	var height int = int(win.GetSystemMetrics(win.SM_CYSCREEN));
	if width == 0 || height == 0 {
		//fmt.Println( "errore" )
		return 2000, 2000; 
	}	
	width  = width  - 20;  // subtraction to make room for any decorations 
	height = height - 40;  // subtraction to make room for any decorations 
	
	return width, height
}
	
//=========================


//-------------------------
func read_dictionary_folder( myDir string) {	
	
    dir, err := os.Open( myDir )
    if err != nil {
		msg1:= `la cartella <span style="color:blue;">` + myDir + "</span> non esiste"				
		if myDir == "" {
			msg1 = "nessuna cartella è stata specificata"		
			msg1 += "<br>" + `per specificare la cartella usa il parametro "directory_folder" nel file ` + 	inputFileList
		}	
		errorMSG = `<br><br> <span style="color:red;">` + msg1 + `</span>` 			
		fmt.Println(msg1);		
		sw_stop = true 
		return		
    }

    files, err := dir.Readdir(-1)
    if err != nil {
        log.Fatal(err)
    }
	fileToReadList := make( []string, 0, 0);	
    for _, f := range files {
        fmt.Println("  dictionary file to read: ", f.Name())
		fileToReadList = append(fileToReadList, f.Name() );  
    }
	sort.Slice(fileToReadList, func(i, j int) bool {
		return fileToReadList[i] < fileToReadList[j]
	})	
	
	//------------------------------
	showReadFile = ""
	for _, ff := range fileToReadList {	
		if ff == langFile {
			read_dictLang_file( myDir  +  string(os.PathSeparator) + ff );	 
		}
		if len(ff) < 5 { continue } 
		switch( ff[0:5] ) {
			case "dictR" :
				read_dictRow_file( myDir  +  string(os.PathSeparator) + ff );	
			case "dictL" :
				read_dictLemmaTran_file( myDir  +  string(os.PathSeparator) + ff );	
		}
		if sw_stop {return}
	}
	fmt.Println("\ntotal number of dictionary lines = ", numberOfDictLines  , "\n"); 
	
}  // end of readDir
//--------------------------------

func read_dictLang_file(ff string) {

	content, err := os.ReadFile(ff)
	if err != nil {
		fmt.Println("error1 in reading file dictionary '" + ff + "'" )			
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
				`<span style="color:blue;">` + ff + `</span>`	+
				`<br><span style="font-size:0.7em;">(` + 	" read_dict_file()" +  ")" + "</span>"
		sw_stop = true 
		return		
    }
	lineD := strings.Split(  string(content),  "\n")
	lineZ := ""
	prevRunLanguage = ""	
	for z:=0; z< len(lineD); z++ { 
		lineZ = strings.TrimSpace(lineD[z]) 
		if lineZ == "" { continue }
		if lineZ[0:9] == "language=" {			
			prevRunLanguage = lineZ[9:] 			
		}
	}	
}// end of read_dictLang_file		


		
//--------------------------------

func read_dictRow_file(ff string) {
	content, err := os.ReadFile(ff)
	if err != nil {
		fmt.Println("error2 in reading file dictionary '" + ff + "'" )			
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
				`<span style="color:blue;">` + ff + `</span>`	+
				`<br><span style="font-size:0.7em;">(` + 	" read_dict_file()" +  ")" + "</span>"
		sw_stop = true 
		return		
    }
	lineD := strings.Split(  string(content),  "\n")
	lineZ := ""
	
	prevRunLanguage = ""
	//prevRunListFile = ""
	var rowDict rDictStruct
	for z:=0; z< len(lineD); z++ { 
		lineZ = strings.TrimSpace(lineD[z]) 	
		if lineZ == "" { continue }
		//fmt.Println("read_dictRow() z=", z, " lineZ=" + lineZ); 
		k1:= strings.Index(lineZ,";")
		ix1, err := strconv.Atoi( lineZ[0:k1] )		
		if err != nil {	continue }	
		rowDict.rdIxRow    = ix1   	
		rowDict.rdTran     = lineZ[k1+1:]   
		dictionaryRow = append( dictionaryRow , rowDict) 
	}
	
	numberOfRowDictLines += len(lineD) 
	fmt.Println( len(lineD) , " lines of ", ff);  	
	
} // end of  read_dictRow_file
//--------------------------------

func read_dictLemmaTran_file(ff string) {

	content, err := os.ReadFile(ff)
	if err != nil {
		fmt.Println("error3 in reading file dictionary '" + ff + "'" )			
		errorMSG = 	`<br><br> <span style="color:red;">errore nella lettura del file </span>` +
					`<span style="color:blue;">` + ff + `</span>`	+
					`<br><span style="font-size:0.7em;">(` + 	" read_dictLemmaTran_file()" +  ")" + "</span>"		
		sw_stop = true 
		return		
    }
	
	// 	abnutzbarkeit vestibilità   ==>  lemma     \t traduzione                                                                   |    |  |        
	
	lineD := strings.Split(  string(content),  "\n")
	lineZ := ""
	
	var ele1 lemmaTranStruct       //  lemmaTranStruct: dL_lemmaCod string,  dL_lemma2 string, dL_tran string  
	
	//---------------
	cod1:= "" 	
	for z:=0; z< len(lineD); z++ { 
		
		lineZ = strings.TrimSpace(lineD[z]) 
		
		// eg. abnutzbarkeit \t	vestibilità     ==>  lemma \t translation  
		
		if lineZ == "" { continue }
		j1:= strings.Index(lineZ, "|")
		if j1 < 0 { continue }
		cod1 = lineZ[0:j1]
		ele1.dL_lemmaCod = newCode(cod1) 
		ele1.dL_lemma2   = strings.TrimSpace( cod1 )
		ele1.dL_tran  = strings.TrimSpace( lineZ[j1+1:] ) 
		/**
		if ele1.dL_lemma2 == "erklären" {   //antonio123
			fmt.Println("ANTONIO CARICA dictL cod1=", cod1 ,  " ele1.dL_lemmaCod=" + ele1.dL_lemmaCod + ", lemma2=" +  ele1.dL_lemma2 +",  tran=", ele1.dL_tran); 
		}
		**/
		
		dictLemmaTran = append( dictLemmaTran, ele1 ) 	
		
	}	
	
	fmt.Println( len(dictLemmaTran) , "  lemma - translation elements of  dictLemmaTran" , "( input: ", ff, ")"  )   
	
} // end of read_dictLemmaTran_file  


//---------------------------------------


func read_lemma_file( inpLemmaFile string) {
	content, err := os.ReadFile( inpLemmaFile )
	if err != nil {
		fmt.Println("error4 in reading file word-lemma '" + inpLemmaFile + "'" )			
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
				`<span style="color:blue;">` + inpLemmaFile + `</span>`	+
				`<br><span style="font-size:0.7em;">(` + 	" read_lemma_file()" +  ")" + "</span>"
		sw_stop = true 
		return		
    }
	lineS := strings.Split(  string(content),  "\n")
	
	var wordLemma1 lemmaStruct
	numLemmaDict=0; 
	
	for z:=0; z< len(lineS); z++ { 
		lineZ0 := strings.TrimSpace(lineS[z]) 
		
		//if z < 5 { fmt.Println("read_lemma_file() ", z, " lineS[]=", lineS[z]) } 
		
		if lineZ0 == "" {continue}
		lineZ := strings.ReplaceAll( lineZ0, "\t" , " ")  // space as separator
		j1:= strings.Index(lineZ, " ")
		if j1 < 0 { continue }	
		wordLemma1.lWord2   = strings.TrimSpace(lineZ[0:j1])
		wordLemma1.lWordCod = newCode( wordLemma1.lWord2)
		wordLemma1.lLemma  = strings.TrimSpace( lineZ[j1+1:]) 
	
		if wordLemma1.lLemma == "-" { continue } 
		wordLemmaPair = append(wordLemmaPair, wordLemma1 ) 
		numLemmaDict++
	}
	fmt.Println( "caricate " , numLemmaDict ,  " coppie word-lemma dal file ", inpLemmaFile, "\n")
	
	//----------------------------------------------------
	/***
	sort.Slice(wordLemmaPair, func(i, j int) bool {
			if (wordLemmaPair[i].lWordCod != wordLemmaPair[j].lWordCod) {
				return wordLemmaPair[i].lWordCod < wordLemmaPair[j].lWordCod
			} else {
				if (wordLemmaPair[i].lWord2 != wordLemmaPair[j].lWord2) {
					return wordLemmaPair[i].lWord2 < wordLemmaPair[j].lWord2 
				} else {
					return wordLemmaPair[i].lLemma < wordLemmaPair[j].lLemma
				}
			}
		} )		 
	//--------------------------
	***/
	
} // end of  read_lemma_file
//---------------------------------

//----------------------

func sort_lemmaTran() {

	sort.Slice(dictLemmaTran, func(i, j int) bool {
			return dictLemmaTran[i].dL_lemmaCod < dictLemmaTran[j].dL_lemmaCod 
		} )	

	/**
	fmt.Println("sort_lemmaTran() inizio") 
	for g2:=0; g2 < len(dictLemmaTran); g2++ {
		if dictLemmaTran[g2].dL_lemma2 == "erklären" {
			fmt.Println(" trovato nel sort  dictLemmaTran[",g2, "] = " , dictLemmaTran[g2] )
		}
	}  
	fmt.Println("sort_lemmaTran() fine") 
	***/
	
} // end of sort_lemmaTran() 

//-------------------------

func addRowTranslation() int {
	
	// add translated rows to the entries of inputTextRowSlice ( same index )  
	
	var len1 = len(inputTextRowSlice)
	numTran:=0
	var rowDict rDictStruct;
	
	for z:=0; z < len(dictionaryRow); z++ {  
		
		/**
		2;Primo capitolo
		4;Gustav Aschenbach o von Aschenbach, come ha fatto sin dai suoi cinquant'anni
		5;compleanno, era il suo nome ufficiale, era l'uno
		**/
		rowDict = dictionaryRow[z] 
		ixRow:= rowDict.rdIxRow	
		if ixRow >= len1 { return 0 }  // error 
		inputTextRowSlice[ixRow].rTran1 =  rowDict.rdTran
		numTran++
	}		
	return numTran
	
} // end of addRowTranslation()
		
//===========================================================================

func fromLemmaTo3List( lemma string) (string, string, string) { 

		fromIx, toIx  := lookForAllParadigma( lemma ) 
		
		//fmt.Println( "         fromIx=", fromIx, "  toIx=", toIx )
		
		listLev := ""
		listPara:= ""
		listExam:= ""		
		for ix:= fromIx; ix <= toIx; ix++ {
			listLev  += "|" + lemma_para_list[ix].p_level   
			parad    := lemma_para_list[ix].p_para			
			if len(parad) > 2 { 				
				if parad[0:lenFseq] == fseq {
					parad = parad[lenFseq:] 
				}
			}
			listPara += "|" + parad  		 	
			listExam += "|" + lemma_para_list[ix].p_example 	
	 		//fmt.Println("\t ", ix, " listLev =", listLev)    
		}	
		if toIx >= fromIx {
			listLev = listLev[1:]
			listPara= listPara[1:]	
			listExam = listExam[1:]	
		}
		return listLev, listPara, listExam 
		
} // end of fromLemmaTo3List 		

//===========================================================================
func addWordLemmaTranLevelParadigma() {
	
	fmt.Println("addWordLemmaTranLevelParadigma()" )
	
	newWordLemmaPair = make( []lemmaStruct, 0, 0 )	
	var newWL lemmaStruct   // 	lWordCod string, lWord2 string , lLemma string
	list1Level:= ""
	list1Para := ""
	list1Exam := ""	
	var wP lemmaTranStruct  
	
	//var swMio bool = false
	
	for zz:=0; zz < len(uniqueWordByFreq); zz++ {
		wF:= uniqueWordByFreq[zz]
		
		lemmaListFound := lookForAllLemmas( wF.uWord2 ) // at least get one element
		nele := len(lemmaListFound)
		
	
		lis_lemma := make( [] string, 0, nele )		
		lis_tran  := make( [] string, 0, nele )
		lis_level := make( [] string, 0, nele )
		lis_para  := make( [] string, 0, nele )
		lis_exam  := make( [] string, 0, nele )
		
		
		newWL.lWord2   = uniqueWordByFreq[zz].uWord2
		newWL.lWordCod = newCode( newWL.lWord2 )
		
		//swMio = (newWL.lWord2 == "erklären")   //antonio123
		
		// each word can have many lemmas 
		//                       each lemma can have many levels, paradigmas, translations ( they are separated by "|", eg "A1|A2|B1" ) 
		for  _, lem := range lemmaListFound {
			list1Level, list1Para, list1Exam = fromLemmaTo3List( lem )
			lis_lemma = append( lis_lemma, lem        )
			lis_level = append( lis_level, list1Level )
			lis_para  = append( lis_para , list1Para  )
			lis_exam  = append( lis_exam , list1Exam  )
			ixTra := lookForAllTran( lem ) 
			if ixTra >= 0 { 
				wP = dictLemmaTran[ixTra] 
				lis_tran = append( lis_tran, wP.dL_tran ) 			
			} else {
				lis_tran = append( lis_tran, ""         ) 		
			}	
			if sw_rewrite_wordLemma_dict { 
				newWL.lLemma = lem 
				newWordLemmaPair = append( newWordLemmaPair, newWL ) 
			}			
		} // end of for , lem 
		
		//if swMio {  fmt.Println("ANTONIO  word=", newWL.lWord2, " uLemmaL=" , lis_lemma, ",    tran=", lis_tran) }
		
		wF.uLemmaL = make( []string,  nele, nele )    
		wF.uTranL  = make( []string,  nele, nele )  
		wF.uLevel  = make( []string,  nele, nele )   
		wF.uPara   = make( []string,  nele, nele )   
		wF.uExample = make( []string, nele, nele )   
		
		copy( wF.uLemmaL  , lis_lemma ) 
		copy( wF.uTranL   , lis_tran  )  
		copy( wF.uLevel   , lis_level ) 
		copy( wF.uPara    , lis_para  ) 
		copy( wF.uExample , lis_exam  ) 
		uniqueWordByFreq[zz] = wF
		
		//if swMio {  fmt.Println("ANTONIO  2 wF=", wF) }
		
	}  // end of for zz 
	//-----------
	
	if len(lemmaNotFoundList) > 0 {
		outFile := dictionaryFolder  +  string(os.PathSeparator) + outLemmaNotFound;
		writeList( outFile, lemmaNotFoundList )		
	}
	
	//countWordLemmaUse() 
	
} // end of addWordLemmaTranLevelParadigma

//-----------------------------------
func stat_level( lemmaLevel []string, numWords int) {	
	
	// get the first level of the first lemma 
	
	if len(lemmaLevel) < 1 { return }
	
	level2 := strings.Split( lemmaLevel[0], "|" ) 
	if len(level2) < 1 { return }
	
	levelToText := level2[0]
	
	sw_oth:=true
	for m:=0; m < len(list_level); m++ {	
		if levelToText == list_level[m] {
			only_level_numWords[m] += numWords 
			sw_oth = false; 
			break
		} 
	} 
	if sw_oth {
		only_level_numWords[0] += numWords 
	}
	
}
//------
func add_ixWord_to_WordSliceFreq() {
	var ixFromList, ixToList int
	tot:=0
	for ixWord:=0; ixWord < len(uniqueWordByFreq); ixWord++ {		
		xWordF := uniqueWordByFreq[ixWord] 			
		stat_level( xWordF.uLevel, xWordF.uTotRow)		
		tot+=  xWordF.uTotRow
		ixFromList = xWordF.uIxWordFreq 
		ixToList   = ixFromList + xWordF.uTotRow;
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wordSliceFreq[n1].wIxUniq = ixWord 			
		} 	
	}  
	
	fmt.Println(" num. words tutte = ", tot) 
	
	/**
	percA0  =  only_A0 * 100 / tot ;     
	percA1  =  only_A1 * 100 / tot ;     
	percA2  =  only_A2 * 100 / tot ;     
	percB1  =  only_B1 * 100 / tot ;     
	percOth =  only_Ot* 100 / tot ;   
	
	fmt.Println(
		  " num. words A0 = ", only_A0,    " \t", percA0 , "%" , 
		"\n num. words A1 = ", only_A1,    " \t", percA1 , "%" ,       
		"\n num. words A2 = ", only_A2,    " \t", percA2 , "%" ,       
		"\n num. words B1 = ", only_B1,    " \t", percB1 , "%" ,        
		"\n num. words altro= ", only_Ot, " \t", percOth, "%"  ) 
	***/	
	
	for f:=1; f < len( only_level_numWords ) ; f++ {
		if only_level_numWords[f] == 0 { continue }
		perc_level[f] = only_level_numWords[f] * 100 / tot ;     
		fmt.Println(" num. words ", list_level[f], " = ", only_level_numWords[f],    " \t", perc_level[f] , "%" ) 
	}	

	if only_level_numWords[0] > 0 {  
		perc_level[0] = only_level_numWords[0] * 100 / tot ;     
		fmt.Println(" num. words ", list_level[0], " = ", only_level_numWords[0],    " \t", perc_level[0] , "%" ) 	
	}

	
} // end of add_index_toWordSliceFreq

//---------------
//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

func lookForAllTran ( lemma30 string ) int {
	lemma3Cod:= newCode(lemma30)	
	fromIxX, toIxX := lookForTranslation( lemma3Cod )
	if toIxX < 0 { return -1 }
	/**
	if lemma30 == "erklären" {
		fmt.Println(" lookForAllTran (", lemma30, ")  lemma3Cod=", lemma3Cod , "  fromIxX=", fromIxX, " toIxX=", toIxX)
		for g2:=fromIxX-3; g2 <= toIxX+3; g2++ {
			fmt.Println(" lookForAllTran () g2=",g2, ",  if dictLemmaTran[k].dL_lemmaCod=", dictLemmaTran[g2] )
		}  
	}
	**/
	
	z:=-1
	fromIx:= fromIxX
	for k:= fromIxX; k >= 0; k-- {
		if dictLemmaTran[k].dL_lemmaCod == lemma3Cod {
			z=k
			break	
		}
		if dictLemmaTran[k].dL_lemmaCod < lemma3Cod { break }
		fromIx = k
	}
	if z < 0 {
		for k:= fromIx; k < len( dictLemmaTran); k++ {
			if dictLemmaTran[k].dL_lemmaCod == lemma3Cod {
				z=k
				break
			}
		} 
	}
	/*** 
	if lemma30 == "erklären" {
		if z > 0 {	
			fmt.Println(" z=", z , " dictLemmaTran[z]=", dictLemmaTran[z]) 
		} else { 	fmt.Println(" z=", z ) }
	}
	***/
	if z < 0 { return -1 }
	
	return z 
	
} // end of lookForAllTran

//-----------------------------

func lookForTranslation(lemmaToFindCod string) (int, int) {

	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := len(dictLemmaTran) - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if dictLemmaTran[median].dL_lemmaCod < lemmaToFindCod {  
			low = median + 1
		}else{
			high = median - 1
		}
	} 
	//---
	fromIx:= low; toIx := high; 
	if fromIx > toIx { fromIx = high; toIx = low;}
	if fromIx < 0 { fromIx=0} 
	if toIx  > maxIx { toIx = maxIx}
	
	return fromIx, toIx	

} // end of lookForTranslation


//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
//------------------------------------------
func lookForAllLemmas(  wordToFind string) []string {

	wordToFindCod:= newCode( wordToFind )	
	lemmaList := lookForAllLemmas2(  wordToFindCod ) 
	if len(lemmaList) > 0 {
		return lemmaList
	}
	
	inp1:= strings.ReplaceAll( 
				strings.ReplaceAll( 
						strings.ReplaceAll( 
							strings.ReplaceAll( wordToFind, "ae","ä"),  
							"oe","ö"), 
						"ue","ü"), 		
				"ss","ß") 	
				
	wordToFindCod2 := newCode( inp1 )
	lemmaList2 := lookForAllLemmas2(  wordToFindCod2 ) 
	if len(lemmaList2) == 0 {
		lemmaList2 = append( lemmaList,  wordToFind )	// if lemma is missing use the original word to find 
		lemmaNotFoundList = append( lemmaNotFoundList, wordToFind ) 
	} 
	return lemmaList2 
	
} // end of lookForAllLemmas
//------------------------------------------
func lookForAllLemmas2(  wordToFindCod string) []string {

	//wordToFindCod:= newCode( wordToFind )

	// get the index of a word in word-lemma dictionary (-1 if not found)  
	var lemmaList = make( []string, 0,0) 
	fromIxX, _ := lookForWordLemmaPair(wordToFindCod)
	fromIx:= fromIxX
	for k:= fromIxX; k >= 0; k-- {
		if wordLemmaPair[k].lWordCod < wordToFindCod { break }
		fromIx = k
	}
	for k:= fromIx; k < len(wordLemmaPair); k++ {
		if wordLemmaPair[k].lWordCod == wordToFindCod {
			lemmaList = append( lemmaList,  wordLemmaPair[k].lLemma )	
		} else {
			if wordLemmaPair[k].lWordCod > wordToFindCod { break }
		}
	} 
			

	//fmt.Println("lookForLemma( ==>" + wordToFind + "<== lemmaList=" , lemmaList, "   numLemmaDict=" , numLemmaDict)
	
	return lemmaList 	
	
} // end of lookForAllLemmas2

//-----------------------------

func lookForWordLemmaPair(wordToFindCod string) (int, int) {
	
	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := numLemmaDict - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if wordLemmaPair[median].lWordCod < wordToFindCod {  
			low = median + 1
		}else{
			high = median - 1
		}
	} 
	//---
	fromIx:= low; toIx := high; 
	if fromIx > toIx { fromIx = high; toIx = low;}
	if fromIx < 0 { fromIx=0} 
	if toIx  > maxIx { toIx = maxIx}
	return fromIx, toIx	

} // end of lookForWordLemmaPair
//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
//------------------------------------------
/****
func countWordLemmaUse() {
	
	ixList:= [9]int{ 1000, 2000, 3000, 4000,5000,6000,7000,8000,9000 }
	
	for i:=0; i < len( ixList); i++ {
		if ixList[i] >= len(uniqueWordByFreq) { countLemma( len(uniqueWordByFreq)-1 ) ; break}
		countLemma( ixList[ i] ) 
	}   
} 
//-----------------	
func countLemma(ixMax int) { 			
		
		accum:= make([]wordIxStruct , 0,0 )
		if ixMax >  len(uniqueWordByFreq) {  ixMax = len(uniqueWordByFreq) }
		for zz:=0; zz < ixMax; zz++ {	
			accum = append( accum, uniqueWordByFreq[zz]  ) 
		}
		//----
		sort.Slice(accum, func(i, j int) bool {
			return accum[i].wLemma < accum[j].wLemma
		})	
		//---
		preL := ""; numLem:=0;
		var oneR  wordIxStruct
		oneR = accum[0]
		preL = oneR.wLemma 
		for zz:=0; zz < ixMax; zz++ {	
			oneR = accum[zz]
			if oneR.wLemma != preL { 
				numLem++
				preL = oneR.wLemma
			} 
		}
		numLem++
		//fmt.Println( "CONTA LEMMA: ", ixMax, " parole,"  , numLem, " lemma")       
		
} // end of countLemma
***/
//------------------

func writeAllUsedRowsOfFile2() {
	
	var swWriteUsedRow = (maxNumLinesToWrite > 0)
	
	fmt.Println("maxNumLinesToWrite=" ,  maxNumLinesToWrite, " swWriteUsedRow =", swWriteUsedRow)
	
	var maxNum = 100
	if swWriteUsedRow { maxNum = maxNumLinesToWrite }
		
	var strOut = ""
	
	nOut  :=0
	nOut0 :=0
	nOut1 :=0 
	
	listMax := [10]int {10, 20, 30, 40, 50, 60, 70, 80, 90, 100}
	
	fmt.Println("\nwriteAllUsedRowsOfFile2() swWriteUsedRow=" , swWriteUsedRow , " countNumLines=" ,countNumLines ); 
	
	if  swWriteUsedRow == false {		
		if countNumLines == false { return }
		for z:= 0; z < len(listMax); z++ {   	
			findHowManyUsedRowsOfFile2( listMax[z] )
		}
		fmt.Println("\nxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n" )
		return
	}
			
	for ixWord:= 0; ixWord < len(uniqueWordByFreq); ixWord++ {
		var xWordF     = uniqueWordByFreq[ ixWord ]  		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNum 		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			//if wS1.nFile == 0  { continue }  
			ixRR:= wS1.wIxRow
			isUsedArray[ ixRR ] = true
			//rowX := inputTextRowSlice[ixRR].row1		
		}
	}	
	//----------------------
	nOut  =0
	nOut0 =0
	nOut1 =0 
	for n2:= 0; n2  < len(inputTextRowSlice); n2++ {
		if isUsedArray[n2] {
			nOut++
			if inputTextRowSlice[n2].rNfile1 == 0 {
				nOut0++
			} else { 
				nOut1++
				if swWriteUsedRow {
					strOut += inputTextRowSlice[n2].rRow1 + "\n"
				}
			}
		} 
	}
	fmt.Println( "\nxxxxxxxxxxxxxxxxxxxxxx\nnumber of rows used (maxNum=", maxNum, ")\nmain text file =\t", nOut0, "\nother text file =\t", nOut1, "\nall text files =\t", nOut, "\nxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n" )
	
	if swWriteUsedRow {		
		outFileName := "wrk_USED_ROWS.txt"
		
		f, err := os.Create( outFileName )
		check(err)
		defer f.Close();

		_, err = f.WriteString( strOut )
		check(err)
		fmt.Println(" file ", outFileName , " written\n") 
	}
	
} // end of writeAllUsedRowsOfFile2
//-------------------------------------------

func findHowManyUsedRowsOfFile2( maxNum int ) {
	
	nOut  :=0
	nOut0 :=0
	nOut1 :=0 
		
	for ixWord:= 0; ixWord < len(uniqueWordByFreq); ixWord++ {
		var xWordF     = uniqueWordByFreq[ ixWord ]  		
		var ixFromList = xWordF.uIxWordFreq 
		var ixToList   = ixFromList + xWordF.uTotRow;
		var maxTo1     = ixFromList + maxNum 		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			//if wS1.nFile == 0  { continue }  
			ixRR:= wS1.wIxRow
			isUsedArray[ ixRR ] = true
			//rowX := inputTextRowSlice[ixRR].row1		
		}
	}	
	//----------------------
		nOut  =0
		nOut0 =0
		nOut1 =0 
		for n2:= 0; n2  < len(inputTextRowSlice); n2++ {
			if isUsedArray[n2] {
				nOut++
				if inputTextRowSlice[n2].rNfile1 == 0 {
					nOut0++
				} else { 
					nOut1++
				}
			} 
		}
		fmt.Println( "\nxxxxxxxxxxxxxxxxxxxxxx\nnumber of rows used (maxNum=", maxNum, ")\nmain text file =\t", nOut0, 
			"\nother text file =\t", nOut1, "\nall text files =\t", nOut) 
		
		
} // end of findHowManyUsedRowsOfFile2	

//------------------------ 
	
func progr_comment(comm1 string) {
	timeNow := time.Now();  
	difft   := timeNow.Sub(timeBegin);  
	diffSec := difft.Seconds()
	timeProgrPerc := int( diffSec*100 / totElapsed)   
	//if timeProgrPerc == prev_timeProgrPerc { return }
	//prev_timeProgrPerc = timeProgrPerc	
	fmt.Printf( "XXX TIME %s perc %d%%, Seconds: %f\n", comm1,  timeProgrPerc, diffSec)
} 
//-------------------
func progressivePerc(swPrt bool, perc int, comm1 string) {

	if swPrt { 
		timeNow := time.Now();  
		difft   := timeNow.Sub(timeBegin);  
		diffSec := difft.Seconds()	
		fmt.Printf( "XXX TIME %s, \t Seconds: %f\n", comm1,  diffSec) 
	}
	
	if perc <= prevPerc { return }		

	//progr_comment(comm1)	

	if sw_HTML_ready {
		go_exec_js_function( "showProgress", strconv.Itoa(perc) ) 	
	}
	prevPerc = perc				
	
} // end of progressivePerc

//---------------------------

func rewrite_word_lemma_dictionary() {	
	
	//----------------------------------------------------
	sort.Slice(newWordLemmaPair, func(i, j int) bool {
			if (newWordLemmaPair[i].lWordCod != newWordLemmaPair[j].lWordCod) {
				return newWordLemmaPair[i].lWordCod < newWordLemmaPair[j].lWordCod
			} else {
				if (newWordLemmaPair[i].lWord2 != newWordLemmaPair[j].lWord2) {
					return newWordLemmaPair[i].lWord2 < newWordLemmaPair[j].lWord2 
				} else {
					return newWordLemmaPair[i].lLemma < newWordLemmaPair[j].lLemma
				}
			}
		} )		 	
	//------------			
	outFile := dictionaryFolder  +  string(os.PathSeparator) + outWordLemmaDict_file ;		
	
	lines:= make([]string, 0, 10+len(newWordLemmaPair) )

	lines = append(lines,  "__" + outFile + "\n" + "_word _lemma ")
	
 	for z:=0; z < len( newWordLemmaPair); z++ {
		//lines = append(lines,  newWordLemmaPair[z].lWord2 + "|" + newWordLemmaPair[z].lLemma) 
		lines = append(lines,  newWordLemmaPair[z].lWordCod + "|" + newWordLemmaPair[z].lWord2 + 
			"|" + newWordLemmaPair[z].lLemma) 
	}  	
	
    writeList( outFile, lines )
	
	
} // end of 

//--------------------------------

func rewrite_wordDict_file() {
						
	outFile := dictionaryFolder  +  string(os.PathSeparator) + outLemmaTranDict_file ;

	pkey := ""; key := ""
	
	lines:= make([]string, 0, 10+len(dictLemmaTran) )
	lines = append(lines,  "__" + outFile + "\n" + "_lemma	_traduzione")
	
	for z:=0; z < len(dictLemmaTran); z++ {
		pkey=key
		
		//if dictLemmaTran[z].dL_lemma2 == dictLemmaTran[z].dL_tran { continue }
		
		key = dictLemmaTran[z].dL_lemma2 + "|"  + dictLemmaTran[z].dL_tran  		
		if pkey == key { continue}
		
		lines = append(lines, key ) 
	}
	writeList( outFile, lines )
	
} // end of rewrite_wordDict_file

//---------------------------

func rewrite_rowDict_file() {

	outFile := dictionaryFolder  +  string(os.PathSeparator) + outRowDict_file;	 
	
	nout:=0  
	lines:= make([]string, 0, 10+len( inputTextRowSlice) )
	
	for z:=0; z < len( inputTextRowSlice); z++ {
		rxTran := inputTextRowSlice[z].rTran1
		if rxTran != "" {		
			lines = append(lines, strconv.Itoa(z) +  "; " + rxTran )  
			nout++
		}	
	}  
	fmt.Println("wrote ", nout , " lines on ", outFile )  
	
	writeList( outFile, lines )

} // end of rewrite_rowDict_file

//----------------------------------------
func console( str1 string) {
	go_exec_js_function( "js_go_console", str1 ) 	
}
//-----------------------------------------------


//--------------------------------

func read_ParadigmaFile() { 
	dat, err := os.ReadFile( inpParaFile )
	if err != nil {
		fmt.Println("error5 in reading file paradigma file '" + inpParaFile + "'" )			
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
					`<span style="color:blue;">` + inpParaFile + `</span>`	+
				`<br><span style="font-size:0.7em;">(` + 	" read_ParadigmaFile()" +  ")" + "</span>"			
		sw_stop = true 
		return		
    }
	/*
		ab  | A2 | abholen, holt ab, hat abgeholt |Wann kann ich die Sachen bei dir abholen<br>Wir müssen noch meinen Bruder abholen  | 
	     0  | 1  |                 2              |                                  3                                                |                                                                  |    |  |        
	*/ 
	
	righe   = strings.Split(  string(dat), "\n") 
	
	fmt.Println("\nletti paradigma file ", inpParaFile  + " " , len(righe) , " righe")   
	
	lemma_para_list = make([]paraStruct, 0, len(righe)+4 )   
	var wP paraStruct
	//var pP paraStruct
	var pkeyL, keyL string
	sk:=0
	//--------------
	for z1:=0; z1 < len(righe); z1++ {		
		col := strings.Split(righe[z1], "|") 	
		if len(col) < 4 { continue }	
		wP.p_lemma   = strings.TrimSpace( col[0] )
		wP.p_level   = strings.TrimSpace( col[1] ) 
		wP.p_para    = strings.TrimSpace( col[2] ) 	
		
		keyL = wP.p_lemma + "." + wP.p_level + "." + wP.p_para 
		if keyL == pkeyL { sk++; continue }
		pkeyL = keyL

		level1 := " " +  wP.p_level + " "
		if strings.Index(list_level_str, level1) < 0 { list_level_str += level1 } 	
		
		if wP.p_para != "" {
			//    0 = x48, A = x65, Z =x90,  a = x97
			ch1 := wP.p_para[0:1]
			if ch1 < "a" { 
				if ch1 < "A" || ch1 > "Z" {
					wP.p_para = fseq + wP.p_para  // per la chiave di sort,  serve per spostare la riga alla fine  se il paradigma inizia con ( [ o altro 
				}	 
			}
		} 
		wP.p_example = strings.TrimSpace( col[3] ) 	
		
		//if wP.p_lemma == pP.p_lemma &&  wP.p_level == pP.p_level { continue } 
		
		//pP = wP ;  
		lemma_para_list = append(lemma_para_list , wP ) 	
		
	} // end of for_z1	
	//------------
	fmt.Println("    scartate ", sk, " righe doppie, ", len( lemma_para_list ), " righe caricate in lemma_para_list")
	
	list_level = strings.Split(strings.TrimSpace(list_level_str), " ") 
	
	fmt.Println("XXX livelli: string=>" + list_level_str + "<== \nlivelli=", list_level) 
	
	only_level_numWords = make([]int, len(list_level), len(list_level) )
	perc_level          = make([]int, len(list_level), len(list_level) )
	
	sort_lemmaPara()  
	
} // end of read_ParadigmaFile

//-----------------------------------------------

func sort_lemmaPara() {

	sort.Slice(lemma_para_list, func(i, j int) bool {
		if lemma_para_list[i].p_lemma != lemma_para_list[j].p_lemma {
			return lemma_para_list[i].p_lemma < lemma_para_list[j].p_lemma         // lemma ascending order (eg.   a before b ) 
		} else {
			if lemma_para_list[i].p_level != lemma_para_list[j].p_level {
				return lemma_para_list[i].p_level < lemma_para_list[j].p_level     // level ascending order (eg.   A1 before A2 ) 
			} else {
				return lemma_para_list[i].p_para < lemma_para_list[j].p_para       // level ascending order (eg.   a  before b ) 
			}
		}	
	} )	

} // end of sort_lemmaPara() 

//--------------------

func lookForAllParadigma( lemma3 string ) (int, int) {
		
	fromIxX, toIxX := lookForParadigma(lemma3 )
	if toIxX < 0 { return -1, -99999 }
	
	
	minIx:= -1; maxIx := -1 

	fromIx:= fromIxX
	
	// get the smaller index  with the right lemma  
	
	for k:= fromIx; k >= 0; k-- {
		if lemma_para_list[k].p_lemma == lemma3 {
			minIx=k
		} else { 
			if lemma_para_list[k].p_lemma < lemma3 { break }
		}
	}
	
	// get the maximum index with the right lemma
	maxIx = minIx
	for k:= fromIx+1; k < len( lemma_para_list); k++ {
		if lemma_para_list[k].p_lemma == lemma3 {
			maxIx = k; 
			if minIx < 0 { minIx = k}
		}  else { 
			if lemma_para_list[k].p_lemma > lemma3 { break }
		}
	}	
	if maxIx < 0 { maxIx = -9999; minIx = -1 } 
	return minIx, maxIx
	
} // end of lookForAllParadigma

//-------------------------------------
func lookForParadigma(lemmaToFind string) (int, int) {

	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := len(lemma_para_list) - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if lemma_para_list[median].p_lemma < lemmaToFind {  
			low = median + 1
		}else{
			high = median - 1
		}
	} 
	//---
	fromIx:= low; toIx := high; 
	if fromIx > toIx { fromIx = high; toIx = low;}
	if fromIx < 0 { fromIx=0} 
	if toIx  > maxIx { toIx = maxIx}
	
	return fromIx, toIx	
	
} // end of 

//-----------------------------

func read_one_inputFileText( fileName string, nFile int) int {
	
    //--------------------------
    // leggi file di testo 
    //-------------------------	
    
	fileName = strings.ReplaceAll(fileName,"\\","/") 
	
    file, e := os.Open(fileName)
    if e != nil {  		
		msg1:= "errore nella lettura del file " + fileName;
		nFileStr1 := strconv.Itoa( nFile )
		
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
				`<span style="color:blue;">` + fileName + `</span>` +
				`<br><span style="font-size:0.7em;">(` + 	" read_one_inputFileText()" + " nFile=" + nFileStr1 + ")" + "</span>"
		
		fmt.Println( msg1)
		sw_stop = true;  
		return -1; 			
    }
    defer file.Close(); //  chiudi il file appena hai finito di leggere  
    //--------------------------------------	
	nBufErr       := 0 
	numErrorLimit := 2	
	buffSize      := 4*1024
	//---------------------------------------
    r := bufio.NewReaderSize(file, buffSize )
	//-------------------------------------	
	
	prevFileNumRow:= numberOfRows
	
	var rS1 rowStruct;
	//----
	rS1.rRow1   = "---"
	inputTextRowSlice = append(inputTextRowSlice, rS1);		// to avoid index 0 	
	isUsedArray       = append(isUsedArray, false)          // to avoid index 0
	if sw_ignore_newLine {  
		rS1.rRow1   = ""
		inputTextRowSlice = append(inputTextRowSlice, rS1);		// to avoid index 0 	
		isUsedArray       = append(isUsedArray, false)          // to avoid index 0
	}
	numberOfRows++; 	
	//---------------------------------------------
	numLinesRead:=0	
	line:=""
	//---------------------------------------------
	//   get one line at time from buffer  and  copy text on inputTextRowSlice 
	//--------------------------------------------------------------------------	
    for true {
		line0, isPrefix, err := r.ReadLine()	
		if isPrefix {
			nBufErr++ 
			fmt.Println("\nXXXXXXXXXXXX  buffer size ", buffSize, " is too small  to read file ", fileName, " (",numLinesRead , " lines already read)")			
			if nBufErr > numErrorLimit {   
				fmt.Println("XXXXXXXXXXXX  too many buffer size errors")
				break
			}
			continue
		}
		if err != nil {
			break
		}
		numLinesRead++ 
		line = strings.ReplaceAll( string(line0), "<br>", "\n")
		//--------------------------------------
		//  sw_ignore_newLine = true  ,   sw_nl_only = true      ==>  incompatibili
		//  sw_ignore_newLine = true  ,   sw_nl_only = false     ==>  split .?!;  
		//  sw_ignore_newLine = false ,   sw_nl_only = false     ==>  split .?!;  and  new line  
		//  sw_ignore_newLine = false ,   sw_nl_only = true      ==>  only new line 
		//------------------------------------------------------------------------------		
		if sw_nl_only {                      // append read line 
			numberOfRows++
			rS1.rRow1   = line  
			rS1.rNfile1 = nFile
			inputTextRowSlice = append(inputTextRowSlice, rS1);			
			isUsedArray       = append(isUsedArray, false)			
			continue
		}
		//--------------------------------------
		split1:= splitHoldSep( string(line) )  //split the line according to several separators (eg.  .;?! )  
		//--------------------------------------
		if sw_ignore_newLine {                 //  sw_ignore_newLine = true  ,   sw_nl_only = false     ==>  split .?!;   											
			for c1, row1 := range split1 {				
				if c1 == 0  {				
					inputTextRowSlice[ len(inputTextRowSlice)-1].rRow1 += " " + row1  // append text to the previous entry 
				} else {	
					numberOfRows++; 
					rS1.rRow1   = row1;
					rS1.rNfile1 = nFile
					inputTextRowSlice = append(inputTextRowSlice, rS1);			
					isUsedArray       = append(isUsedArray, false)			
				}	
			}	
			continue
		} 
		//---------------------------------------
		//  sw_ignore_newLine = false ,   sw_nl_only = false     ==>  split .?!;  and  new line   											
		for _, row1 := range split1 {
			numberOfRows++; 
			rS1.rRow1   = row1;
			inputTextRowSlice = append(inputTextRowSlice, rS1);			
			isUsedArray       = append(isUsedArray, false)				
		}			
    } // end of for true 
	//--------------------------
	if nFile == 0 {  // append read line 
			numberOfRows++
			rS1.rRow1   = LAST_WORD
			rS1.rNfile1 = 0
			inputTextRowSlice = append(inputTextRowSlice, rS1);			
			isUsedArray       = append(isUsedArray, false)					
	} 
	
	numLinesAppended := numberOfRows - prevFileNumRow;
	fmt.Println( "\n", numLinesRead, " rows read from text file ", fileName , "\n\t", numLinesAppended, " rows appended on slice" )
	
	//rogressivePerc(true,   17 , "read file " + strconv.Itoa(nFile) + ", line=" + strconv.Itoa(numberOfRows)   )
	/**
	for g1:=0; g1 < len(inputTextRowSlice); g1++ {
		fmt.Println("ROW ", g1, " => ", inputTextRowSlice[g1] ) 
	}
	**/
	return numLinesAppended; 
	
} // end of read_one_inputFileText 
//---------------------------------------


// xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

//----------------------------------------
func buildSeparRowlist() {
	separRow1 := separRow
	if separRow1[:1] == "[" { separRow1 = separRow1[1:] }
	if separRow1[ len(separRow1)-1:] == "]" { separRow1 = separRow1[0: len(separRow1)-1] }
	
	fmt.Println("separ =", separRow )
	fmt.Println("separ1= ", separRow1)
	
	for _, chr1 := range separRow1 {
		separRowList = append(separRowList, string(chr1) ) 
	}	
	fmt.Println("\n separRowList=", separRowList)
	
}	
//---------------------------	
func splitHoldSep( str1 string) []string {
	/*
	split string according to several separator characters
	keeping them in the text  	
	*/
	
	if len(separRowList)== 0 { buildSeparRowlist() }
	
	newY  := str1   
	split1:= []string{}
	for  _, sep1:= range separRowList {    
		split1 = strings.SplitAfter(newY, sep1)
		newY   = strings.Join(split1[:], "§")
	}
	return strings.Split(newY, "§")
	
} // end of  splitHoldSep	
	
//--------------------------------------

//----------------------
func writeList( fileName string, lines []string)  {
	// create file
    f, err := os.Create( fileName )
    if err != nil {
        log.Fatal(err)
    }
    // remember to close the file
    defer f.Close()

    // create new buffer
    buffer := bufio.NewWriter(f)

    for _, line := range lines {
        _, err := buffer.WriteString(line + "\n")
        if err != nil {
            log.Fatal(err)
        }
    }
    // flush buffered data to the file
    if err := buffer.Flush(); err != nil {
        log.Fatal(err)
    }
} 
//----------------------------------------

//----------------------------
func newCode( inpCode string ) string {	
	/*
	1) serve soprattutto per mettere le parole in sequenza alfabetica coerente 
		( es. per il tedesco es.  ä, ö, ü, ß vicini rispettivamente ad a, o, u, ss)   
	2) a volte ä, ö, ü, ß sono scritti come ae, oe, ue, ss, in questo caso li sostituiamo con a, o, u, ss
    3) a volte eu dovrebbe rimanere tale (es. Treue), non ho modo di distinguere per cui la sequenza è falsata ue è prima di ua o di uz 
		l'alternativa potrebbe essere tradurre ü con ue, ma questo porterebbe alla sequenza errata  ue nel posto ua, ue, uz invece di u ua uz
	----------
	questo codice di sequenza   è usato per word e lemma
	la scrittura alternativa a quella ufficiale (es. ue invece di ü) può essere trovata in un testo.
	Il lemma si trova in un file "ufficiale"  quindi improbabile che venga usata la scrittura alternativa.

	a) nel lemma il newCode mi serve soltanto per correggere la sequenza
	b) nel word (che si trova nel testo analizzato) il new code mi serve per confrontare 
		però è probabile che un testo sia scritto o in codice alternativo o in modo normale, improbabile in entrambi modi. 
	c) si potrebbe pensare ad un switch da impostare ????
	d) cosa devo confrontare?
		lemma ( non mi serve tradurre eventuale codice alternativo, però newCode mi serve per la sequenza )
			confronto per collegarlo a word e per trovare la traduzione
		word  ( confronto per assegnare il lemma )       	
	
	*/
	inp1:= strings.ReplaceAll( 
						strings.ReplaceAll( 
							strings.ReplaceAll(inpCode, "ae","a"),  
							"oe","o"), 
						"ue","u") 		
	inp2:= strings.ReplaceAll( 
					strings.ReplaceAll( 
						strings.ReplaceAll( 
							strings.ReplaceAll(inp1, "ä","a"),  
							"ö","o"), 
						"ü","u"), 
					"ß","ss")   
	return inp2 + "." + inpCode  // 21Nov2023
	
}// end of newCode					
//--------------------------------	