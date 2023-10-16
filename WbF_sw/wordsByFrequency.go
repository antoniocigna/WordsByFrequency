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
    "regexp"
    "sort"
    "bufio"	
    "github.com/zserge/lorca"	
	"github.com/lxn/win"
)

//----------------------------------
var timeBegin  = time.Now()
var totElapsed = 12.200 

var lastPerc=0; 
var prevPerc = -1; 
//---------------
var	html_path        string = "WBF_html_jsw"
var inputFileList    string = "inputFileList.txt";     // file listing all input files 
var langFile         string = "language.txt"           // lang and voice file    
var dictionaryFolder string = ""  //   prevRunDictionaryAndVoice";
var lemmaFile        string = ""  //   lemma_file.txt";  
var sw_rewrite_wordLemma_dict bool = false
var sw_rewrite_word_dict bool = false
var sw_rewrite_row_dict  bool = false
var outWordLemmaDict_file = "newWordLemmaDict.txt";
var outLemmaTranDict_file = "newLemmaTranDict.txt"
var outRowDict_file  = "newRowDict.txt"
var sw_ignore_newLine bool = false

const wSep = "§";                         // used to separe word in a list 
const endOfLine = ";;\n"

//------
var parameter_path_html string  = "WBF_html_jsw"
//------------------

type rowStruct struct {
    row1        string
	nFile1      int  
	swExtra     bool 
    numWords    int
	listIxUnF   []int 
	listFreq    []int   
	tran1       string 
}

//--
type wordStruct struct {       // a word is repeated several time one for each row containing it  
    word     string
	sw_ignore bool
	ixUniq   int               // index of uniqueWordByFreq      
	nFile    int 
    ixRow    int       
	ixPosRow int 
	totRow   int 
	totMinRow int
	totWrdRow int 
}
//--
type wordIxStruct struct {
    word       string	
	ixUnW      int            // index of this word in the uniqueWordByFreq	
	ixUnW_al   int            // index of this word in the uniqueWordByAlpha 	
	totRow     int 
    ixWordFreq int            // index of this word in the wordSliceFreq	
	wLemmaL    []string       // list of lemma 
	wTranL     []string       // list of translation    
}	
//---
type lemmaStruct struct {
	lWord  string 
	lLemma string
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
	rIxRow  int 
	rTran   string 
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
	dL_lemma string 
	dL_tran  string 
} 
//---------------
type lemmaWordStruct struct {
	lw_lemma string 	
	lw_word  string 
	lw_ix    int
}
//-------------------------------------------
var separRow   = "[\r\n.;:?!]";
var separRowFalse = "[\r\n]";
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
//----------------------------------------					
//var wordSliceAlpha = make([]wordStruct,4323146,4400000)  
//var wordSliceFreq  = make([]wordStruct,4323146,4400000)  

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

		// A simple way to know when UI is ready (uses body.onload event in HTML/JS)
		ui.Bind("goStart", func() { 
				sw_HTML_ready = true 
				if sw_begin_ended {
					bind_goStart()
				}	
			} )
		//--------------
		ui.Bind("go_passToJs_wordList", func(fromWord int, numWords int, js_function string) {
				bind_go_passToJs_wordList(fromWord,  numWords, js_function)  })
				
		//--------------------------------------
		ui.Bind("go_passToJs_prefixWordList", func(numWords int, wordPrefix string, js_function string) {
				bind_go_passToJs_prefixWordList( numWords, wordPrefix, js_function) } ) 
		
		//---------------------------------------
		ui.Bind("go_passToJs_lemmaWordList", func(lemma string, js_function string) {
				bind_go_passToJs_lemmaWordList(lemma, js_function) } ) 

		//---------------------------------------
		ui.Bind("go_passToJs_getWordByIndex", func( ixWord int, maxNumRow int, js_function string) {
				bind_go_passToJs_getWordByIndex( ixWord, maxNumRow, js_function) } ) 

		//---------------------------------------
		ui.Bind("go_passToJs_thisWordRowList", func( aWord string, maxNumRow int, js_function string) {
				bind_go_passToJs_thisWordRowList( aWord, maxNumRow, js_function) } )
		
		//---------------------------------------
		ui.Bind("go_passToJs_rowList", func( inpBegRow int, maxNumRow int, js_function string) {
				bind_go_passToJs_rowList( inpBegRow, maxNumRow, js_function) } )
		
		//---------------------------------------
		ui.Bind("go_passToJs_rowWordList", func( numIdOut string, numId int, js_function string ) {
				bind_go_passToJs_rowWordList(numIdOut, numId, js_function) } ) 	
				
		//---------------------------------------	
		ui.Bind("go_write_lang_dictionary", func( langAndVoiceName string) {
			bind_go_write_lang_dictionary( langAndVoiceName ) } )  

		//---------------------------------------	
		ui.Bind("go_write_word_dictionary", func( listGoWords string) {
			bind_go_write_word_dictionary( listGoWords ) } )  
				
		//---------------------------------------			
		ui.Bind("go_write_row_dictionary", func( listGoRows string) {
			bind_go_write_row_dictionary( listGoRows ) } )  
		
		//------
}  

//---------------------------------------------
func bind_goStart() {
		//fmt.Println("\nXXXXXXX GO XXXXXXX  goStart xxxxxxxxxxxxx è stato lanciato da 'onload()' nel file  HTML\n" );  
		//fmt.Println("\nXXXXXXX GO XXXXXXX  buildStatistics() xxxxxxxxxxxxx " );  	
		
		buildStatistics()
		
		mainNum := strconv.Itoa(numberOfUniqueWords) +";" + strconv.Itoa(numberOfWords) + ";" + strconv.Itoa(numberOfRows) +"))" 
		
		
		go_exec_js_function("js_go_showReadFile", mainNum + showReadFile);  
		
		//fmt.Println("\nXXXXXXX GO XXXXXXX  js_go_ready() xxxxxxxxxxxxx " );  
		
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

func bind_go_passToJs_wordList(fromWord int, numWords int, js_function string) {
		
		var from1, to1 int; 
		from1 = fromWord - 1; 
		if (from1 < 0) {from1=0;}
		if (from1 >= numberOfUniqueWords) {from1 = numberOfUniqueWords - 1;}		
		to1 = numWords + from1; 
		if (to1 > numberOfUniqueWords)   {to1 = numberOfUniqueWords;}	 
				
		var xWordF wordIxStruct;  
		var outS1 string = ""; 
		//var row11 string;
		//var numNoTran = 0
		
		//console("bind_go_passToJs_wordList() 0 "  ) 	
		
		for i:= from1; i < to1; i++ { 
			xWordF = uniqueWordByFreq[i] 
			outS1 += xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" + 
					 fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep) ) + endOfLine 
			
		}			
		//row11 = ",-1," +  strconv.Itoa( numNoTran) + ",numNoTran";   	
		//outS1 += strings.TrimSpace( row11 ); 
		
		go_exec_js_function( js_function, outS1 ); 	
	
		//go_exec_js_function( js_function, strings.ReplaceAll( outS1, "`", " ")); //   outS1 ); 	
					
}  // end of bind_go_passToJs_wordList	

//------------------------------------------------------

func bind_go_passToJs_prefixWordList( numWords int, wordPrefix string, js_function string) {
	
		var outS1 string; 
		from1, to1 := searchAllWordWithPrefixInAlphaList( wordPrefix )
		//var row11 string;
		//fmt.Println( "go_passToJs_prefixWordList ret da search... from1=" , from1 , "  to1=", to1)
		//var numNoTran = 0   
		if (to1 < 0) {
			outS1 = "NONE," + wordPrefix ; // nessuna parola che inizia con " + wordPrefix;
		} else {	
			//zz:=0
			for i:=from1; i <=to1; i++ {	
				xWordF:=  uniqueWordByAlpha[i] 
				
				row11 := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" + 
						fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep)) + endOfLine   
				outS1 += row11
					
			}
		}
		//row11 = ",-1," +  strconv.Itoa( numNoTran) + ",numNoTran";   	
		//outS1 += row11 ; 
		
		//fmt.Println( "go_passToJs_prefixWordList chiama go_exec_js_function( " + js_function + ", outS1=" + outS1);  
		
		go_exec_js_function( js_function, outS1 ); 		
	
			
} // end of bind_go_passToJs_prefixWordList

//----------------------------------------------
func bind_go_passToJs_lemmaWordList(lemmaToFind string, js_function string)   {
	
		outS1 := "" 
		
		
		fromIxX, _ := lookForLemmaWord( lemmaToFind)
		
		fromIx:= fromIxX
		for k:= fromIxX; k >= 0; k-- {
			if lemma_word_ix[k].lw_lemma < lemmaToFind { break }
			fromIx = k
		}
		for k:= fromIx; k < len(lemma_word_ix); k++ {
		
			if lemma_word_ix[k].lw_lemma == lemmaToFind {		
				ix := lemma_word_ix[k].lw_ix 	
				xWordF:=  uniqueWordByFreq[ix] 				
				row11 := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" + 
						fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep)) + endOfLine   
				outS1 += row11			
			} else {
				if lemma_word_ix[k].lw_lemma > lemmaToFind { break }
			}
		} 
		if len(outS1)< 3 {
			outS1 = "NONE," + lemmaToFind; 			
			//fmt.Println(" bind_go_passToJs_lemmaWordList() ", outS1) 
		} 	
		
		go_exec_js_function( js_function, outS1 ); 		
				
} // end of bind_go_passToJs_lemmaWordList

//----------------------------------------
func bind_go_passToJs_getWordByIndex( ixWord int, maxNumRow int, js_function string) {
		
		var outS1 string; 
		//ixWord--; 
		if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}	
		
		var xWordF     = uniqueWordByFreq[ixWord]   
		
		var ixFromList = xWordF.ixWordFreq 
		var ixToList   = ixFromList + xWordF.totRow;
		var maxTo1     = ixFromList + maxNumRow; 		
		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
			
		preRow := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" 
		lemmaList := xWordF.wLemmaL
		tranList  := xWordF.wTranL
		for z:=0; z < len(lemmaList); z++  {
			//row11 := preRow +  lemmaList[z]+ "," + tranList[z] + ";"
			outS1 += preRow +  lemmaList[z]+ ";" + tranList[z] + endOfLine 
		}	
		preIxRR := -1
		/*
		here are scanned all the rows containing the word required (with index ixWord) 
		for each line totMinRow is the number of words in the line with lower reference than the required word (ie. not studied yet)	
		*/
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			ixRR:= wS1.ixRow
			if (ixRR == preIxRR) { continue;} 
			preIxRR = ixRR; 
			if ixRR >= numberOfRows { continue;} // actually there  must be some error here 
			
			rline := inputTextRowSlice[ixRR]
			rowX := rline.row1					
			outS1 += "<br>;;" + strconv.Itoa(wS1.nFile) + ";;" + strconv.Itoa(wS1.ixRow) +				
				 ";; " + cleanRow(rowX) + ";; " + rline.tran1; 				
		} 	
		
		go_exec_js_function( js_function, outS1 ); 	
		
}   // end of bind_go_passToJs_getWordByIndex 

//----------------------------------------------

func bind_go_passToJs_thisWordRowList( aWord string, maxNumRow int, js_function string) {
		//fmt.Println(" in go esegue go_passToJs_thisWordRowList( aWord=", aWord, " maxNumRow=" , maxNumRow);  
		
		var outS1 string;
		
		//fmt.Println( "cerca ", aWord);
		
		var xWordF wordIxStruct;  
		ix := searchOneWordInAlphaList( aWord ) 
		
		if (ix < 0) {
			//fmt.Println( aWord, "\t NOT FOUND "); 
			outS1 += "NONE," + aWord  
			go_exec_js_function( js_function, outS1 ); 	
		} else {
			xWordF =  uniqueWordByAlpha[ix] 
			//fmt.Println( aWord, "\t found  ",  xWordF.word, " ix=", ix,   " totRow=", xWordF.totRow, " ixwordFre=", xWordF.ixWordFreq); 
			 
			ixWord := xWordF.ixUnW
			
			if ixWord >= numberOfUniqueWords {ixWord = numberOfUniqueWords - 1;}	
			
			xWordF     = uniqueWordByFreq[ixWord]   

			//fmt.Println("bind_go_passToJs_thisWordRowList()" ,  aWord, "\t found  ",  xWordF.word, " ixWord=", ixWord,   " totRow=", xWordF.totRow, " ixwordFre=", xWordF.ixWordFreq); 
			
			var ixFromList = xWordF.ixWordFreq 
			var ixToList   = ixFromList + xWordF.totRow;
			var maxTo1     = ixFromList + maxNumRow; 		
			
			if ixToList > maxTo1        { ixToList = maxTo1; }
			if ixToList > numberOfWords { ixToList = numberOfWords; }	
							
			preRow := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" 
			lemmaList := xWordF.wLemmaL
			tranList  := xWordF.wTranL
			for z:=0; z < len(lemmaList); z++  {
				//row11 := preRow +  lemmaList[z]+ "," + tranList[z] + ";"
				outS1 += preRow +  lemmaList[z]+ ";" + tranList[z] + endOfLine 
			}	
			
			/**
			row11  := xWordF.word + ";" + strconv.Itoa(xWordF.ixUnW) + ";" + strconv.Itoa(xWordF.totRow)  + ";" + 
					 fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep) ) + endOfLine 
	
			//row11 := xWordF.word + "," + strconv.Itoa(xWordF.ixUnW) + "," + strconv.Itoa(xWordF.totRow)  + ";" + 
			//	fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + ";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep)) + endOfLine   	
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
				ixRR:= wS1.ixRow
				if (ixRR == preIxRR) {continue;} 
				preIxRR = ixRR; 
				nn++;
				if ixRR >= numberOfRows { continue;} // actually there  must be some error here 
				rline := inputTextRowSlice[ixRR]
				rowX := rline.row1		
		
				outS1 += "<br>;;" + strconv.Itoa(wS1.nFile) + ";;" + strconv.Itoa(wS1.ixRow) +
					 ";; " + cleanRow(rowX) + ";; " + rline.tran1;  
			}
			go_exec_js_function( js_function, outS1 ); 	
		}
		
}    // end of bind_go_passToJs_thisWordRowList 
//-----------------------------------------------------

func bind_go_passToJs_rowList( inpBegRow int, maxNumRow int, js_function string) {

	var ixFromList = inpBegRow 
	var ixToList   = ixFromList + maxNumRow
		
	var maxTo1     = ixFromList + maxNumRow; 		

	if ixToList > maxTo1        { ixToList = maxTo1; }
	if ixToList > len(inputTextRowSlice) { ixToList = len(inputTextRowSlice) }		
	var outS1 string;

	for ixRR := ixFromList; ixRR < ixToList; ixRR++  {
		rline := inputTextRowSlice[ixRR]
		//if rline.nFile1 != 0 { continue}
		rowX := rline.row1	
		outS1 += "<br>;;" + strconv.Itoa( rline.nFile1) + ";;" + strconv.Itoa( ixRR) + ";; " + cleanRow(rowX) + ";; " + rline.tran1;  
	} 	
	
	go_exec_js_function( js_function, outS1 ); 	
			
} // end of bind_go_passToJs_rowList


//------------------
func bind_go_passToJs_rowWordList(numIdOut string, numId int, js_function string) {
		
	ixRR := numId
	if ixRR >= len(inputTextRowSlice) { ixRR = len(inputTextRowSlice) - 1 }
	
	rowX := inputTextRowSlice[ixRR]

	outS1:= numIdOut + "," + strconv.Itoa(numId) + endOfLine
	
	for w:=0; w < len(rowX.listIxUnF); w++ {  
		ixWord := rowX.listIxUnF[w] 
	
		xWordF := uniqueWordByFreq[ixWord] 
		
		row11 := xWordF.word + "," + strconv.Itoa(xWordF.ixUnW) + "," + 
			strconv.Itoa(xWordF.totRow)  + ";" + 
			fmt.Sprint( strings.Join(xWordF.wLemmaL, wSep) ) + 
			";" + fmt.Sprint( strings.Join(xWordF.wTranL, wSep)) + 
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
		
		if listGoWords[0:9] == "language=" { return }
		
		
		lemmaTranStr := "__" + outFileName + "\n" + "_lemma	_traduzione"
		
		lemmaTranStr += split_ALL_word_dict_row( listGoWords )		
				
		f, err := os.Create( outFileName )
		check(err)
		defer f.Close();

		_, err = f.WriteString( lemmaTranStr );  
		check(err) 

		f.Sync()
		
		//----------------------
		
		sort_lemmaTran() ;  // tulizzabili già in questo run 
		
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
	
	return field[0], ix1, lemmaLis, tranLis 
		
} // end of	split_one_Word_Dict_row(	

//-------------------------------

func split_ALL_word_dict_row(  strRows string) string {
	
	// eg. einem;14 ; ein einem einer ;  a uno uno;	  ==> word ; ix : list of lemmas ; list of translations	
	
	lemmaTranStr := ""
	
	lines := strings.Split( strRows, "\n");	
	
	var ele1 lemmaTranStruct     
	
	
	for z:=0;  z < len(lines); z++ {   
		_, ix1, lemmaLis,tranLis := split_one_word_dict_row( lines[z] )
		if ix1 < 0 { continue }		
		
		if uniqueWordByFreq[ix1].ixUnW != ix1 {	continue }  // error	
		
		//swUpdList[ix1] = true 
		//numUpd++  		
		ixAlfa := uniqueWordByFreq[ix1].ixUnW_al  	
		
		len1:= len(uniqueWordByFreq[ix1].wLemmaL)
		if len1 != len(lemmaLis) { continue }               // error 
		if len1 != len(tranLis)  { continue }               // error 
		for m:=0; m < len1; m++ {
			mLemm := strings.TrimSpace( lemmaLis[m] )
			mTran := strings.TrimSpace( tranLis[m] 	)	
			uniqueWordByFreq[ix1].wTranL[m]      = mTran 					
			uniqueWordByAlpha[ixAlfa].wTranL[m]  = mTran 		 
			uniqueWordByAlpha[ixAlfa].wLemmaL[m] = mLemm	
			
			lemmaTranStr += "\n" + mLemm + " " + mTran 	
			
			ele1.dL_lemma = mLemm 
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
		
		if uniqueWordByFreq[ix1].ixUnW != ix1 { continue } 
		
		swUpdList[ix1] = true 
		numUpd++  
		
		ixAlfa = uniqueWordByFreq[ix1].ixUnW_al   		
		lemmaLis := uniqueWordByFreq[ix1].wLemmaL
		
		for m:=0; m < len(lemmaLis); m++ {
			if lemma1 == lemmaLis[m] {
				uniqueWordByFreq[ix1].wTranL[m]      = wordTran 					
				uniqueWordByAlpha[ixAlfa].wTranL[m]  = wordTran 
				uniqueWordByAlpha[ixAlfa].wLemmaL[m] = lemma1
				//if ix1 == 17 {  fmt.Println("\t\tm=", m, ", tran[]=", uniqueWordByFreq[ix1].wTranL[m]  ) }
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
		lemmaLis := sU.wLemmaL
		tranLis  := sU.wTranL
		/**
		if ix1 == 17 {
			fmt.Println( " uniqueWordByFreq[ix1]=",  uniqueWordByFreq[ix1] )
			fmt.Println("\tlemmaL =",uniqueWordByFreq[ix1].wLemmaL, "\n\ttranL=",  uniqueWordByFreq[ix1].wTranL ) 
		}
		**/
		
		lemmS:= ""; tranS:=""
		for m:=0; m < len(lemmaLis); m++ {
			lemmS += "," +lemmaLis[m]
			tranS += "," +tranLis[m]
			//if ix1 == 17 {fmt.Println( " lemmS=" + lemmS, "  \t ", " tranS=", tranS) }
		}	
		lemmS += " " ; tranS += " "
		newStr += sU.word + ";" + strconv.Itoa(ix1) + ";" +
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
		inputTextRowSlice[ixRow].tran1 = tranS
		
		//fmt.Println("\t?? anto inputTextRowSlice[ixRow] = ", inputTextRowSlice[ixRow] )
		numTran++
	}		
	return numTran
	
} // end of writeRowDictTranslation

//------------------------------------------
/**
func update_words_tran( newTranWordStr string) {
	if newTranWordStr == "" {return}
	//												listNewTranWords += "\n" + word1 + "," + ix1 + "," + wordTran ;   // new line for dictionary 
	wordTranList := strings.Split(newTranWordStr, "\n") 	
	
	var word1, ixS, wordTran string
	var ixAlfa int
	
	for i:= 0; i < len(wordTranList); i++ {
		col1:= strings.Split( wordTranList[i], ",")
		if len(col1) != 3 { continue}  
		word1    = col1[0]
		ixS      = col1[1]
		wordTran = col1[2]
		ix1, err := strconv.Atoi(ixS)
		if err != nil { continue} 
		
		if uniqueWordByFreq[ix1].ixUnW != ix1 { continue } 
		uniqueWordByFreq[ix1].wLemma = word1
		uniqueWordByFreq[ix1].wTran  = wordTran
		//
		ixAlfa = uniqueWordByFreq[ix1].ixUnW_al   		
		uniqueWordByAlpha[ixAlfa].wLemma = word1
		uniqueWordByAlpha[ixAlfa].wTran  = wordTran
	} 
	
} // end of update_words_tran
**/

//====================================================

func begin() { 	
	
	
	setHtmlEnv();	
	
	progressivePerc(true,   5 ,"1")
	
	readTextFiles(); 
	
	
	if sw_stop == false  {buildWordList() }	   	
	
	if sw_stop == false  {elabWordList() }	
	
	sort_lemmaTran()  
	
	if sw_rewrite_wordLemma_dict { rewrite_word_lemma_dictionary() }
	if sw_rewrite_word_dict { rewrite_wordDict_file() }
 	if sw_rewrite_row_dict {  rewrite_rowDict_file() }	
	
	sw_begin_ended = true 
	
	if sw_HTML_ready {
		bind_goStart()
	}		
	
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
	
	progressivePerc(true,   5 , "start reading text files")
	
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
	
	sw_nl_only  := false	
	var separRow_save = separRow
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
					separRow = strings.ReplaceAll( separRow, "\n", "") 
					separRow = strings.ReplaceAll( separRow, "\r", "") 
					sw_ignore_newLine = true 
					fmt.Println("\tsplit row chars. = " + separRow)  
				}
				
			case "text_split_by_newline_only" :   		
				value1 = strings.ToLower(value1)					
				fmt.Println("text_split_by_newline_only :", value1)  
				if value1 == "true" {  
					separRow = separRowFalse   // use only \n or \r
					sw_nl_only = true 
					fmt.Println("\tsplit row chars. = " + separRow)  
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
				lemmaFile =  strings.ReplaceAll(value1,"\\","/") 				           
				fmt.Println("lemma file        = " + value1 )
			
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
		separRow = separRow_save
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
	fmt.Println("lemma_file        = ", lemmaFile )  
	fmt.Println("")
	
	if len(fileToReadList) == 0 { 
		errorMSG = `<br><br> <span style="color:red;">` +
					`ERROR: non c'è nessun file da leggere</span>`  + 
					`<br>file list ` +  	`<span style="color:blue;">` + inputFileList + `</span>`			
		fmt.Println(errorMSG);		
		sw_stop = true 
		return 			
	}  
	if lemmaFile != ""  {
		read_lemma_file()
	}
	
	read_dictionary_folder( dictionaryFolder )
	if sw_stop { return }
	
	
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
	
//--------------------------------------------------------
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
	
    scanner := bufio.NewScanner(file)
    //------
    //  riempie lo slice inputTextRowSlice 
    //  --- scanner esegue loop sulle righe di testo ( \n = fine riga),  scanner.Text() fornisce una riga   
    //-----
	
	prevFileNumRow:= numberOfRows
	
	var rS1 rowStruct;
	//----
	//lastPercProg: 5; //9.615%
	
	
	inputTextRowSlice = append(inputTextRowSlice, rS1);		// to avoid index 0 	
	isUsedArray       = append(isUsedArray, false)          // to avoid index 0
	numberOfRows++; 
		
	/********************
	** split text line  using the newline and other separation characters (eg .;?! ) 
	********************/
	if sw_ignore_newLine == false {
		for scanner.Scan() {
			split1 := regexp.MustCompile(separRow).Split(scanner.Text(), -1); // crea slice dei pezzi di riga ( separati da . ; ? ! ecc.)  	
			for _, row1 := range split1 {
				numberOfRows++
				rS1.row1   = row1;
				rS1.nFile1 = nFile
				inputTextRowSlice    = append(inputTextRowSlice, rS1);			
				isUsedArray = append(isUsedArray, false)
			}
		}
	}
	if sw_ignore_newLine {
		/********************
		** split text line using the spicified separation characters (eg .;?! ), but IGNORING newline 	
		********************/
		newString := ""
		for scanner.Scan() {
			newString += scanner.Text() +" "
		}		
		split1 := regexp.MustCompile(separRow).Split( newString, -1); // crea slice dei pezzi di riga ( separati da . ; ? ! ecc.)  	
		for _, row1 := range split1 {
			numberOfRows++
			rS1.row1   = row1;	

			//fmt.Println("row1=" + row1); 	
			
			rS1.nFile1 = nFile
			inputTextRowSlice    = append(inputTextRowSlice, rS1);			
			isUsedArray = append(isUsedArray, false)
		}
		newString = ""
	}	
	numLines := numberOfRows - prevFileNumRow;
	fmt.Println( "\n", numLines, " rows read from text file ", fileName )
	
	progressivePerc(true,   17 , "read file " + strconv.Itoa(nFile) + ", line=" + strconv.Itoa(numberOfRows)   )
	
	
	return numLines; 
    //-------------------
	
} // end of readInputText

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
	
	progressivePerc(true,   18 , "buildWordList" )
	
	numberOfWords=0; 
	nn:=0
	
	
	ever0 := float64(0.032051) * float64(  len(inputTextRowSlice) )
	every:= int( ever0 )	
	
	fmt.Println("EVERY ", every , "lines increase 1% time")
	
	lastPerc = 18;
	
	
	for ixR, rS2 := range inputTextRowSlice {	//  for each text row 
		row2   := rS2.row1;
		if every > 0 { 
			if (int(ixR/every)*every) ==  ixR {  lastPerc++; progressivePerc(false,   lastPerc,  "extract words from text: number row=" + strconv.Itoa(ixR) );  }		
		}
		
		wordA  := regexp.MustCompile(separWord).Split(row2, -1);  // split row into words 
        z:= -1;
		for _, wor1 := range wordA {
			wS1.word = strings.ToLower(strings.TrimSpace(wor1));
			if wS1.word == "" || isThereNumber( wS1.word )  {
				continue;
			}			
			z++;
			nn++
			wS1.nFile    = rS2.nFile1 
			wS1.ixRow    = ixR   // index of row containing the word 
			wS1.ixPosRow = z;    // position of the word in the row 
			wordSliceAlpha = append(wordSliceAlpha, wS1);
			
		}
	}
	
	//---------------------------------------
	numberOfWords = len(wordSliceAlpha); 
		
	progressivePerc(true,  44 , "extracted " + strconv.Itoa(numberOfWords) + "words from text" )
		
	fmt.Println("number of words in text lines ", numberOfWords);
	
	//----
	sort.Slice(wordSliceAlpha, func(i, j int) bool {
		if wordSliceAlpha[i].word != wordSliceAlpha[j].word {
			return wordSliceAlpha[i].word < wordSliceAlpha[j].word            // word  ascending order (eg.   a before b ) 
		} else {
			return wordSliceAlpha[i].nFile < wordSliceAlpha[j].nFile          // nFile ascenfing order (eg.   0 before 1 ) 
		}
	})		
	
	progressivePerc(true,  61 ,"words sorted")
	
} // end of buildWordList

//------------------------------------------------

func elabWordList() {
		
	addTotRowToWord()	
	
		progressivePerc(true,  63 , "elab.words 2 finito addRowToWord")
		
	elabWordAlpha_buildWordFreqList() 		
	
		progressivePerc(true,  76 , "elab.words 3 finito elabWordAlpha_buildWordFreqList" )
		
	build_uniqueWord_add_frequence();
	
	putWordFrequenceInRowArray()

	addRowTranslation() 
	
		progressivePerc(true,  79 , "elab.words 4 finito addRowTranslation() " )
	
	build_lemma_word_ix()
		progressivePerc(true,  79 , "elab.words 4 finito add_lemma_word_ix, finito elabWordList" )
	
} // end of elabWordList()

//----------------------------------------------

func addTotRowToWord() {
	/*
	each element of wordSliceAlpha contains a word (the same word may be in several rows) 
	the number of repetition of a word (totRow) is put in its element  ( later will be put in each row that contain it) 
		eg.  one 3, one 3, one 3, two 4, two 4, two 4, two 4	
	*/
	preW  := wordSliceAlpha[0].word;	
	totR  := 0	
	ix1   := 0
	ix2   :=-1
	//----------------
	for i, wS1 := range wordSliceAlpha {
		
		//fmt.Println("ANTO addTot ... i=" , i , " => ", wS1 )
		
		if (wS1.word != preW) {
			ix2 = i; 
			for i2 := ix1; i2 < ix2;i2++ {
				 wordSliceAlpha[i2].totRow = totR;   // se una parola è ripetuta 3 volte, ad ogni parola è associato 3  
			}
			totR = 0
			ix1  = i; 
			preW = wS1.word; 
		} 
		totR++;     	
	}
	ix2++; 
	for i2 := ix1; i2 < len(wordSliceAlpha);i2++ {
		wordSliceAlpha[i2].totRow = totR; 
	}
	//------
	
	
} // end of addTotRowToWord 

//---------------------------------

func elabWordAlpha_buildWordFreqList() {
	/*
	put in each row of the inputTextRowSlice the number of its words  
	from wordSliceAlpha list obtain a new list by sorting it by occurrence of the words (totRow) 
	*/
	preW  := ""; // wordSliceAlpha[0].word;	
	ix:=0;
	removeIxWord :=-1 
	
	for nn, wS1 := range wordSliceAlpha {	
		
		//fmt.Println("ANTO elab...FreqList() nn=", nn, ", preW=" + preW + ",  wS1 ", wS1)  
		
		if (wS1.word != preW) {		
			removeIxWord = -1
			preW = wS1.word; 
			if wS1.nFile > 0 { removeIxWord = nn}
			
			//fmt.Println("\t ANTO 1elab...FreqList() nn=", nn, ", new preW=" + preW + "   removeIxWord=" , removeIxWord)
		}
		ix =  wS1.ixRow
		inputTextRowSlice[ix].numWords ++; 		// how many words contains the row (eg. the row "the cat is on the table"  contains 6 words --> .numWords = 6 
		if removeIxWord >= 0 {
			//fmt.Println("\t ANTO 2elab" , "  removeIxWord=" , removeIxWord , " wordSliceAlpha[ removeIxWord ].word=" + wordSliceAlpha[ removeIxWord ].word  )
			
		    if wS1.word == wordSliceAlpha[ removeIxWord ].word {
				wordSliceAlpha[ nn ].sw_ignore = true 
			}	
		}	
		//fmt.Println("\t ANTO XXXelab"  , "  wS1.sw_ignore = ", wS1.sw_ignore)  
	}
	//------------
	/**
	for nn, wS1 := range wordSliceAlpha {
		fmt.Println("ANTO elabWordAlpha_buildWordFreqList() nn=", nn, ", wS1 ", wS1)  
	}	
	**/
	
	//------------
	// build WordList by frequence in the text
	// the slice is sorted in descending order of frequency   ( ie. firstly the most used)   
	//-----------------------------------
	
	wordSliceFreq  = make([]wordStruct, len(wordSliceAlpha),  len(wordSliceAlpha) ) 	 // la slice destinazione del 'copy' deve avere la stessa lunghezza di quella input  
	
	copy(wordSliceFreq , wordSliceAlpha);
	
	// le parole eguali si trovano in righe contigue perchè hanno la stessa frequenza
	
	sort.Slice(wordSliceFreq, func(i, j int) bool {
		if wordSliceFreq[i].totRow !=  wordSliceFreq[j].totRow {
		   return wordSliceFreq[i].totRow > wordSliceFreq[j].totRow        // totRow    descending order (how many row contain the word) 
		}
		return wordSliceFreq[i].word < wordSliceFreq[j].word               // word      alphabetically ascending order (when totRow is equal)	   	
	})	
	
	
	
} // end of elabWordAlpha_buildWordFreqList

//--------------------------------------

func putWordFrequenceInRowArray() {

	ix:=0;

	//-------------------------	
	//  in each element of inputTextRowSlice define an empty slice to contain the frequence of each of its words
	for k, _ := range inputTextRowSlice {	
		tot1 := inputTextRowSlice[k].numWords;
		inputTextRowSlice[k].listIxUnF =  make( []int, tot1, tot1 )		
		inputTextRowSlice[k].listFreq  =  make( []int, tot1, tot1 )		
	}
	
	//---------------------------------
	//  fill each row with the frequence of its words
	//-------------------	
	
	for _, wS1 := range wordSliceFreq {	
		//fmt.Println("ANTO putWordFrequenceInRowArray() wS1 ", wS1)  
		
		ix = wS1.ixRow; 
		ixPos := wS1.ixPosRow; 
		num2 := len(inputTextRowSlice[ix].listFreq) 
		if (num2 <= ixPos) {		
			fmt.Println("error " , wS1.word, " ix=" , ix  ," ixPos=",   ixPos, " row ", " num2=", num2, " tot1=",  inputTextRowSlice[ix].numWords, " list=" , inputTextRowSlice[ix].listFreq , " " , inputTextRowSlice[ix].row1); 			
		}
		inputTextRowSlice[ix].listIxUnF[ixPos] = wS1.ixUniq // index of the word in the uniqueWordByFreq  	
		inputTextRowSlice[ix].listFreq[ ixPos] = wS1.totRow // for each word in the row  set its frequence of use (how many times the word is used in the whole text)  	
	}
	
	//---------------------------
} // end of putWordFrequenceInRowArray

//------------------------------------------------

func put_a_priority_to_the_row_of_each_word() {
		
	//the row importance is assigned by the number of its unknown words	
	
	progressivePerc(true,  79 , "put a priority"  )
	
	for k, wS1 := range wordSliceFreq {	
		
		ix := wS1.ixRow; 
		numMinor :=0 	
		wordFreq := wS1.totRow; 		
		for _, frw:= range   inputTextRowSlice[ix].listFreq {
			if frw < wordFreq { numMinor++; }
		} 
		wordSliceFreq[k].totMinRow = numMinor;	             // number of words with frequency < this word   	
		wordSliceFreq[k].totWrdRow = inputTextRowSlice[ix].numWords   // number of words in this row    
	}		
	
	progressivePerc(true,  83 , "put a priority sort" ) 
	
	sortWordListByFreq_and_row_priority() 
		
} // end of put_a_priority

//--------------------------------------
func build_uniqueWord_add_frequence() {
	
	progressivePerc(true,  79, "build_uniqueWord_add_frequence 1")
	
	put_a_priority_to_the_row_of_each_word() 	
		
	preW := ""
	numWordUn := 0
	numWordRi := 0	
	num_word:=0
	
	numWordUn_0 := 0
	numWordRi_0 := 0	
	num_word_0 :=0 
	//--------------------
	
	progressivePerc(true,  95 , "build_uniqueWord_add_frequence 2" )
	
	for _, wS1 := range wordSliceFreq {	
			num_word++			
			
			if wS1.sw_ignore == false { 
				num_word_0++
			}
			
			if wS1.word != preW {
				preW = wS1.word;
				numWordUn += 1 
				numWordRi += wS1.totRow 
				if wS1.sw_ignore == false { 
					numWordUn_0 += 1 
					numWordRi_0 += wS1.totRow 
				}
			}  
	}
	progressivePerc(true,  96 , "build_uniqueWord_add_frequence 3" )
	//------------
	if num_word_0 != num_word {
		fmt.Println( "PAROLE SINGOLE File0= ", numWordUn_0, ", PAROLE Totale=", numWordRi_0,  "  numberOfWords=" , num_word_0 , " "  );
	}
	fmt.Println( "PAROLE SINGOLE tutti= ", numWordUn, ", PAROLE Totale=", numWordRi,  "  numberOfWords=" , num_word , "\n");
	
	progressivePerc(true,  97 ,  "build_uniqueWord_add_frequence 4" )
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
	// remove elements to ignore  ( those of the files after the first )
	wrk := wordSliceFreq[:0]
	for _, wS1 := range wordSliceFreq {				
			if wS1.sw_ignore { continue }
			wrk = append( wrk, wS1) 
	}
	
	wordSliceFreq = wrk	
	
	//--------------------
	
	for n1, wS1 := range wordSliceFreq {	
			if wS1.word != preW {
				preW = wS1.word;
					
				xWordF.word = wS1.word;
				xWordF.totRow = wS1.totRow
				xWordF.ixWordFreq = n1
				//xWordF.wTran = "" 
				xWordF.ixUnW     = len(uniqueWordByFreq)  
				uniqueWordByFreq = append( uniqueWordByFreq, xWordF);  
				numWordUn += 1 
							
				numWordRi += wS1.totRow 
				percIx = int(numWordUn * 100 / numberOfUniqueWords); 
				//if percIx < 2 { fmt.Println( percIx, "% parole,  n1=" , n1 , " (ultima=" , xWordF.word, " numWordUn=" , numWordUn, " freq=" , xWordF.totRow, " ", numWordUn * 100 / numberOfUniqueWords, "%"   )}
				
				sS.uniqueWords = numWordUn 
				sS.totWords    = numWordRi
				sS.uniquePerc  = percIx 
				sS.totPerc     = int(numWordRi * 100 / numberOfWords);
				/**
				if strconv.Itoa(1000 + percIx)[3:] == "0" {  
					wordStatistic_un[percIx] = sS; 	
				}
				***/				
				if strconv.Itoa(1000 + sS.totPerc)[3:] == "0" {  	
					wordStatistic_tx[sS.totPerc] = sS; 
				}
				//fmt.Println("STAT. ", n1, " ", xWordF.word, " numWordUn=", numWordUn,  " numWordRi=", numWordRi, " percIx=", percIx, " ", sS.uniquePerc,  " sS.totPerc=" ,  sS.totPerc); 
			}  
			
	}
	
	progressivePerc(true,  98, "add lemma" )	
		
	addWordLemma()   
	
	add_ixWord_to_WordSliceFreq()
	
	progressivePerc(true,   99 , "add translation")
	
	addWordTranslation()		
	
	//---------------------
	uniqueWordByAlpha = make([]wordIxStruct, len(uniqueWordByFreq),  len(uniqueWordByFreq))	 // la slice destinazione del 'copy' deve avere la stessa lunghezza di quella input  
	
	stat_useWord();
	
	copy( uniqueWordByAlpha, uniqueWordByFreq); 
		
	sort.Slice(uniqueWordByAlpha, func(i, j int) bool {
			return uniqueWordByAlpha[i].word < uniqueWordByAlpha[j].word
		} )		
	//console( "\nlista uniqueWordByAlpha")	
	// update alpha index  // ixUnW,  ixUnW_al	
	for u:=0; u < len(uniqueWordByAlpha); u++ {
		f:= uniqueWordByAlpha[u].ixUnW
		uniqueWordByFreq[f].ixUnW_al  = u; 		
		uniqueWordByAlpha[u].ixUnW_al = u
		//console( fmt.Sprintln( "uniqueWordByAlpha ", uniqueWordByAlpha[u] ) )
	}
 	//console( "------------------\n")
	
} // end of build_uniqueWord_add_frequence

//-----------------------
func build_lemma_word_ix() {
	
	//	build a slice with all lemma with all words 
	/*
	lemmaWordStruct struct {lw_lemma string lw_word  string lw_ix    int
	*/
	lemma_word_ix = make([]lemmaWordStruct, 0, 0)  
	
	var wL lemmaWordStruct
	
	for z:=0; z < len(uniqueWordByFreq); z++ {		 	
		wL.lw_word = uniqueWordByFreq[z].word 
		wL.lw_ix   = uniqueWordByFreq[z].ixUnW
		
		lemmaLis :=  uniqueWordByFreq[z].wLemmaL
		
		for m:=0; m <  len(lemmaLis); m++ {
			wL.lw_lemma = lemmaLis[m]   
			lemma_word_ix = append( lemma_word_ix, wL )
		}	
	} 
	//--------------
	// order by lemma and word 	
	sort.Slice(lemma_word_ix, func(i, j int) bool {
			if  lemma_word_ix[i].lw_lemma != lemma_word_ix[j].lw_lemma {
				return lemma_word_ix[i].lw_lemma < lemma_word_ix[j].lw_lemma 	
			}
			return lemma_word_ix[i].lw_word < lemma_word_ix[j].lw_word 		
		} )		
	 
} // end of build_lemma_word_ix  
 

//--------------------------

func sortWordListByFreq_and_row_priority() {

	sort.Slice(wordSliceFreq, func(i, j int) bool {
		if wordSliceFreq[i].totRow !=  wordSliceFreq[j].totRow {
		   return wordSliceFreq[i].totRow > wordSliceFreq[j].totRow        // totRow    descending order (how many row contain the word) 
		}
		if wordSliceFreq[i].word !=  wordSliceFreq[j].word {
		   return wordSliceFreq[i].word < wordSliceFreq[j].word            // word      ascending order	  		   
		}	
		if wordSliceFreq[i].nFile !=  wordSliceFreq[j].nFile {
		   return wordSliceFreq[i].nFile < wordSliceFreq[j].nFile          // nFile     ascending order  ( firstly	file 0)   		   
		}		
		if wordSliceFreq[i].totMinRow !=  wordSliceFreq[j].totMinRow {
		   return wordSliceFreq[i].totMinRow < wordSliceFreq[j].totMinRow  // totMinRow ascending order	(how many words in the row are not yet learned) 
		}
		return wordSliceFreq[i].ixRow < wordSliceFreq[j].ixRow             // ixRow     ascending order	( first the rows which were first in the text)  		   
			
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
		/**
		for _, sS:= range wordStatistic_un[1:] {	
			//fmt.Println( sS.uniqueWords , " words (",  sS.uniquePerc, "%), found ", sS.totWords,  " times in the text(", sS.totPerc,"%)" ) 
			result += "<br>" + fmt.Sprintln( sS.uniqueWords , " words (",  sS.uniquePerc, "%), make up ", sS.totPerc,"% of the text (", sS.totWords, " words)") 
		}  
		result += "<br>===================================================="
		***/
		for _, sS:= range wordStatistic_tx {	
			if sS.totWords == 0 { continue; }
			//fmt.Println( sS.uniqueWords , " words (",  sS.uniquePerc, "%), found ", sS.totWords,  " times in the text(", sS.totPerc,"%)" ) 
			result += "<br>" + fmt.Sprintln( sS.uniqueWords , " words (",  sS.uniquePerc, "%), make up ", sS.totPerc,"% of the text (", sS.totWords, " words)") 
		}  
		
		
	
		//result = "prova, la stringa  vera sembra che sia invalida"
		
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
		
		if uniqueWordByFreq[ixNow].totRow == lastTot { continue }
		
		//fmt.Println("stats ", lisPerc[z], "% = num.Elem.",  listIxPerc[z], " toIx=", ixNow,   " num.Rows per word=",uniqueWordByFreq[ixNow].totRow )
		if listIxPerc[z] >= 1 {
			fmt.Println("stats ", lisPerc[z], "% = num.Elem.",  listIxPerc[z], " sono usate   " , uniqueWordByFreq[ixNow].totRow , " o più volte" , 
				" (", (100 - lisPerc[z]) ,  "% delle parole non sono usate più di ",  uniqueWordByFreq[ixNow].totRow ," volte)" )
		}
		lastTot = uniqueWordByFreq[ixNow].totRow 	
	} 
	
}
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

func searchOneWordInAlphaList(  wordToFind string) int {
	
	// get the index of a word in dictionary (-1 if not found)  
	
	wordToFind = strings.ToLower(strings.TrimSpace( wordToFind));  
	
	fromIx, toIx:= lookForWordInDictionary(wordToFind)
	ix := -1	
	for k:= fromIx; k <= toIx; k++ {
		if uniqueWordByAlpha[k].word == wordToFind {ix=k; break}
	}  	
	
	return ix; 	
	
} // end of searchOneWordInAlphaList

//-----------------------------
func searchAllWordWithPrefixInAlphaList(  wordPref string) (int, int) {
	
	// get the indicies of the first and the last word beginning with the required prefix (-1,-1 if not found)  
	
	wordPref = strings.ToLower(strings.TrimSpace( wordPref));  
	lenPref:= len(wordPref); 
	ixTo := -1; ixFrom:= -1;	
	
	if lenPref == 0 { return ixFrom, ixTo }
	
	ix1, ix2:= lookForWordInDictionary(wordPref)	
	wA :=""
	spaceFill := "                                                          ";  
	//-----------
	for k:= ix1; k >= 0; k-- {
		wA =  uniqueWordByAlpha[k].word + spaceFill
		if wA[0:lenPref] < wordPref { break; }
		ixFrom = k; 
	}  
	
	if (ixFrom >=0) { ixTo = ixFrom; }  //  se ixFrom è valido, deve essere valido anche ixTo   
	
	for k:= ix2; k < numberOfUniqueWords; k++ {
		wA =  uniqueWordByAlpha[k].word + spaceFill  
		if wA[0:lenPref] > wordPref { break; }
		ixTo = k; 
		if (ixFrom < 0) {ixFrom = ixTo;}  //  se ixTo è valido, deve essere valido anche ixFrom   
	}  
	return ixFrom, ixTo 
	
} // end of searchAllWordWithPrefixInAlphaList

//--------------
func lookForWordInDictionary(wordToFind string) (int, int) {

	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := numberOfUniqueWords - 1	
	maxIx := high; 
	//----
	for low <= high{
		median := (low + high) / 2
		if median >= len(uniqueWordByAlpha) {
			fmt.Println("errore in lookForWordInDictionary: median=", median , "     len(uniqueWordByAlpha)=" ,  len(uniqueWordByAlpha) )
		}
		if uniqueWordByAlpha[median].word < wordToFind {
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

} // end of lookForWordInDictionary



//-----------------------------

func lookForLemmaWord(lemmaToFind string) (int, int) {
	
	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := len(lemma_word_ix) - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if lemma_word_ix[median].lw_lemma < lemmaToFind {  
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


//------------------------------------------------------
func testPreciseWord(target string ) {
	fmt.Println( "cerca ", target);
	var xWordF wordIxStruct;  
	ix := searchOneWordInAlphaList( target ) 
	
	if (ix < 0) {
		fmt.Println( target, "\t NOT FOUND "); 
	} else {
		xWordF =  uniqueWordByAlpha[ix] 
		fmt.Println( target, "\t found  ",  xWordF.word, " ix=", ix,   " totRow=", xWordF.totRow, " ixwordFre=", xWordF.ixWordFreq); 
	} 
	fmt.Println( "-------------------------------------------------\n" ); 
} 
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
			fmt.Println( "trovato ", xWordF.word, " ix=", i,   " totRow=", xWordF.totRow, " ixwordFre=", xWordF.ixWordFreq); 
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
			fmt.Println("error in reading file dictionary '" + ff + "'" )			
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

//-----------------------------------
func TOGLIsplitDictWordLine( lineZ2 string ) (string, int, []string, []string ) {		
													            // nuovo formato: 	nome;ix;lemma1§lemma2;traduzione1§traduzione2; 
		                                                        //                  seinem;17;sein§seine§essere,il suo;
																//                     0    1   2           3  											 
		w123  := strings.Split( lineZ2, ";" ) 
		if len(w123) < 4 {  return "",-1,nil,nil }
		word2 := w123[0]	
		ix1, err := strconv.Atoi(  w123[1] )		
		if err != nil {	return "",-1,nil,nil }	
		ix2   := ix1
		//lemma2:= ""
		//tran2:=""
		
		lemmaX := strings.Split( w123[2], ",")
		tranX  := strings.Split( w123[3], ",")
		
		return word2, ix2, lemmaX, tranX  
		
} // end of TOGLIsplitDictWordLine
		
//--------------------------------

func read_dictRow_file(ff string) {
	content, err := os.ReadFile(ff)
	if err != nil {
			fmt.Println("error in reading file dictionary '" + ff + "'" )			
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
		rowDict.rIxRow    = ix1   	
		rowDict.rTran     = lineZ[k1+1:]   
		dictionaryRow = append( dictionaryRow , rowDict) 
	}
	
	numberOfRowDictLines += len(lineD) 
	fmt.Println( len(lineD) , " lines of ", ff);  	
	
} // end of  read_dictRow_file
//--------------------------------

func read_dictLemmaTran_file(ff string) {

	content, err := os.ReadFile(ff)
	if err != nil {
		fmt.Println("error in reading file dictionary '" + ff + "'" )			
		errorMSG = 	`<br><br> <span style="color:red;">errore nella lettura del file </span>` +
					`<span style="color:blue;">` + ff + `</span>`	+
					`<br><span style="font-size:0.7em;">(` + 	" read_dictLemmaTran_file()" +  ")" + "</span>"		
		sw_stop = true 
		return		
    }
	
	lineD := strings.Split(  string(content),  "\n")
	lineZ := ""
	
	var ele1 lemmaTranStruct       //  lemmaTranStruct:  dL_lemma string, dL_tran string  
	
	//---------------
		
	for z:=0; z< len(lineD); z++ { 
		
		lineZ = strings.TrimSpace(lineD[z]) 
		
		// eg. abnutzbarkeit \t	vestibilità     ==>  lemma \t translation  
		
		if lineZ == "" { continue }
		j1:= strings.Index(lineZ, " ")
		if j1 < 0 { continue }
		ele1.dL_lemma = strings.TrimSpace( lineZ[0:j1] )
		ele1.dL_tran  = strings.TrimSpace( lineZ[j1+1:] ) 
		
		dictLemmaTran = append( dictLemmaTran, ele1 ) 	
		
	}	
	
	fmt.Println( len(dictLemmaTran) , "  lemma - translation elements of  dictLemmaTran" , "( input: ", ff, ")"  )    	
	
}
//---------------------------------------
func read_lemma_file() {
	content, err := os.ReadFile( lemmaFile )
	if err != nil {
			fmt.Println("error in reading file word-lemma '" + lemmaFile + "'" )			
		errorMSG = `<br><br> <span style="color:red;">errore nella lettura del file </span>` +
					`<span style="color:blue;">` + lemmaFile + `</span>`	+
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
		wordLemma1.lWord   = lineZ[0:j1]
		wordLemma1.lLemma  = strings.TrimSpace( lineZ[j1+1:]) 
	
		if wordLemma1.lLemma == "-" { continue } 
		wordLemmaPair = append(wordLemmaPair, wordLemma1 ) 
		numLemmaDict++
	}
	fmt.Println( "caricate " , numLemmaDict ,  " coppie word-lemma", "\n")
	
	//----------------------------------------------------
	sort.Slice(wordLemmaPair, func(i, j int) bool {
			if (wordLemmaPair[i].lWord != wordLemmaPair[j].lWord) {
				return wordLemmaPair[i].lWord < wordLemmaPair[j].lWord
			} else {
				return wordLemmaPair[i].lLemma < wordLemmaPair[j].lLemma
			}
		} )		 
	//--------------------------
	
} // end of  read_lemma_file
//---------------------------------
//----------------------
func addWordTranslation() {
	
	for z:=0; z < len(uniqueWordByFreq); z++ {		 	
	
		lemmaLis :=  uniqueWordByFreq[z].wLemmaL
		
		for m:=0; m <  len(lemmaLis); m++ {
			if uniqueWordByFreq[z].wTranL[m] == "" {		
				uniqueWordByFreq[z].wTranL[m] = lookForAllTran( lemmaLis[m] )  
			}
		}	
	} 
} // end of addWordTranslation

//----------------------
func OLD_addWordTranslation_this_func_use_dictw() {
	
	// add translated words to the entries of uniqueWordByFreq slice ( same index )  
	
	numUn  := len(uniqueWordByFreq)
	
	var wordDict wDictStruct;
	
	for z:=0; z < len(dictionaryWord); z++ {
																// nuovo formato: 	nome; ix; lemma1§lemma2;  traduzione1§traduzione2; 
		                                                        //                  seinem;17; sein§seine; essere§il suo;			 	
		wordDict = dictionaryWord[z]
		
		ixS := wordDict.dIxWuFreq		
		if ixS >= numUn || ixS < 0 {
			continue 
		}		
		lemmaLis := uniqueWordByFreq[ixS].wLemmaL
		maxM := len(lemmaLis) 
		if len(wordDict.dLemmaL) < maxM { maxM = len(wordDict.dLemmaL) }
		for m:=0; m < maxM; m++ {
			if wordDict.dLemmaL[m] == lemmaLis[m] {
				uniqueWordByFreq[ixS].wTranL[m] = wordDict.dTranL[m] 
			}
		}	
	} 
} // end of OLDaddWordTranslation

//-----------------------------------

func sort_lemmaTran() {

	sort.Slice(dictLemmaTran, func(i, j int) bool {
			return dictLemmaTran[i].dL_lemma < dictLemmaTran[j].dL_lemma 
		} )	

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
		ixRow:= rowDict.rIxRow	
		if ixRow >= len1 { return 0 }  // error 
		inputTextRowSlice[ixRow].tran1 =  rowDict.rTran
		numTran++
	}		
	return numTran
	
} // end of addRowTranslation()
		
//===========================================================================
//===========================================================================
func addWordLemma() {
	
	fmt.Println("addWordLemma()" )
	
	newWordLemmaPair = make( []lemmaStruct, 0, 0 )	
	var newWL lemmaStruct   // 	lWord  string , lLemma string
	
	for zz:=0; zz < len(uniqueWordByFreq); zz++ {

		lemmaListFound := lookForAllLemmas(  uniqueWordByFreq[zz].word ) // at least get one element
		
		lis_lemma := make( [] string, 0, 0 )
		
		newWL.lWord = uniqueWordByFreq[zz].word
		
		for  _, lem := range lemmaListFound {
			lis_lemma = append( lis_lemma, lem)
			if sw_rewrite_wordLemma_dict { 
				newWL.lLemma = lem 
				newWordLemmaPair = append( newWordLemmaPair, newWL ) 
			}
		}
		//if len(lis_lemma) > 1 {fmt.Println("lemma doppi word=",  uniqueWordByFreq[zz].word, " lemma=" , lis_lemma) }
	
		lis_tran  := make( [] string, len(lis_lemma), len(lis_lemma) )
		
		uniqueWordByFreq[zz].wLemmaL = make( []string, len(lis_lemma), len(lis_lemma) )
		uniqueWordByFreq[zz].wTranL  = make( []string, len(lis_tran),  len(lis_tran ) )
		copy( uniqueWordByFreq[zz].wLemmaL, lis_lemma) 
		copy( uniqueWordByFreq[zz].wTranL,  lis_tran)  //  translation is empty, it will be filled later  
	
	}  
	//-----------
	
	//countWordLemmaUse() 
	
} // end of addWordLemma

//-----------------------------------
func add_ixWord_to_WordSliceFreq() {
	var ixFromList, ixToList int
	
	for ixWord:=0; ixWord < len(uniqueWordByFreq); ixWord++ {	
	
		xWordF := uniqueWordByFreq[ixWord] 
		
		ixFromList = xWordF.ixWordFreq 
		ixToList   = ixFromList + xWordF.totRow;
		if ixToList > numberOfWords { ixToList = numberOfWords; }		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wordSliceFreq[n1].ixUniq = ixWord 			
		} 	
	}  

} // end of add_index_toWordSliceFreq

//---------------
//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

func lookForAllTran ( lemma3 string ) string {
		
	fromIxX, toIxX := lookForTranslation( lemma3 )
	if toIxX < 0 { return "" }
	
	//fmt.Println(" lookForAllTran (", lemma3, ")   fromIxX=", fromIxX, " toIxX=", toIxX)
	
	z:=-1
	fromIx:= fromIxX
	for k:= fromIxX; k >= 0; k-- {
		if dictLemmaTran[k].dL_lemma == lemma3 {
			z=k
			break	
		}
		if dictLemmaTran[k].dL_lemma < lemma3 { break }
		fromIx = k
	}
	if z < 0 {
		for k:= fromIx; k < len( dictLemmaTran); k++ {
			if dictLemmaTran[k].dL_lemma == lemma3 {
				z=k
				break
			}
		} 
	}
	if z < 0 { return "" }
	
	return dictLemmaTran[z].dL_tran
	
} // end of lookForAllTran

//-----------------------------

func lookForTranslation(lemmaToFind string) (int, int) {

	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := len(dictLemmaTran) - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if dictLemmaTran[median].dL_lemma < lemmaToFind {  
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
func lookForAllLemmas(  wordToFind string) []string {
	
	// get the index of a word in word-lemma dictionary (-1 if not found)  
	var lemmaList = make( []string, 0,0) 
	fromIxX, _ := lookForWordLemmaPair(wordToFind)
	fromIx:= fromIxX
	for k:= fromIxX; k >= 0; k-- {
		if wordLemmaPair[k].lWord < wordToFind { break }
		fromIx = k
	}
	for k:= fromIx; k < len(wordLemmaPair); k++ {
		if wordLemmaPair[k].lWord == wordToFind {
			lemmaList = append( lemmaList,  wordLemmaPair[k].lLemma )	
		} else {
			if wordLemmaPair[k].lWord > wordToFind { break }
		}
	} 
	if len(lemmaList) == 0 {
		lemmaList = append( lemmaList,  wordToFind )	// if lemma is missing use the word 
	} 		

	//fmt.Println("lookForLemma( ==>" + wordToFind + "<== lemmaList=" , lemmaList, "   numLemmaDict=" , numLemmaDict)
	
	return lemmaList 	
	
} // end of lookForAllLemmas

//-----------------------------

func lookForWordLemmaPair(wordToFind string) (int, int) {
	
	// find 2 indices of the 2 words nearest to the word to find 
	
	low   := 0
	high  := numLemmaDict - 1	
	maxIx := high; 
	
	//----
	for low <= high{
		median := (low + high) / 2
		if wordLemmaPair[median].lWord < wordToFind {  
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
		var ixFromList = xWordF.ixWordFreq 
		var ixToList   = ixFromList + xWordF.totRow;
		var maxTo1     = ixFromList + maxNum 		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			//if wS1.nFile == 0  { continue }  
			ixRR:= wS1.ixRow
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
			if inputTextRowSlice[n2].nFile1 == 0 {
				nOut0++
			} else { 
				nOut1++
				if swWriteUsedRow {
					strOut += inputTextRowSlice[n2].row1 + "\n"
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
		var ixFromList = xWordF.ixWordFreq 
		var ixToList   = ixFromList + xWordF.totRow;
		var maxTo1     = ixFromList + maxNum 		
		if ixToList > maxTo1        { ixToList = maxTo1; }
		if ixToList > numberOfWords { ixToList = numberOfWords; }
		
		for n1 := ixFromList; n1 < ixToList; n1++  {
			wS1 := wordSliceFreq[n1] 
			//if wS1.nFile == 0  { continue }  
			ixRR:= wS1.ixRow
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
				if inputTextRowSlice[n2].nFile1 == 0 {
					nOut0++
				} else { 
					nOut1++
				}
			} 
		}
		fmt.Println( "\nxxxxxxxxxxxxxxxxxxxxxx\nnumber of rows used (maxNum=", maxNum, ")\nmain text file =\t", nOut0, "\nother text file =\t", nOut1, "\nall text files =\t", nOut) 
		
		
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
		/**
		timeNow := time.Now();  
		difft   := timeNow.Sub(timeBegin);  
		diffSec := difft.Seconds()	
		fmt.Printf( "XXX TIME %s, \t Seconds: %f\n", comm1,  diffSec) 
		**/
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
					
	outFile := dictionaryFolder  +  string(os.PathSeparator) + outWordLemmaDict_file ;
	
	var wordLemmaListStr = "__" + outFile + "\n" + "_word _lemma "
	
	sort.Slice(newWordLemmaPair, func(i, j int) bool {
			if (newWordLemmaPair[i].lWord != newWordLemmaPair[j].lWord) {
				return newWordLemmaPair[i].lWord < newWordLemmaPair[j].lWord
			} else {
				return newWordLemmaPair[i].lLemma < newWordLemmaPair[j].lLemma
			}
		} )		 
	//------------ 
	for z:=0; z < len( newWordLemmaPair); z++ {
		wordLemmaListStr += "\n" + newWordLemmaPair[z].lWord + " " + newWordLemmaPair[z].lLemma
	}  	
	//-----------		
	f, err := os.Create( outFile )
	check(err)
	defer f.Close();
	_, err = f.WriteString( wordLemmaListStr )
	check(err)
	f.Sync()
	
} // end of 

//--------------------------------

func rewrite_wordDict_file() {
						
	outFile := dictionaryFolder  +  string(os.PathSeparator) + outLemmaTranDict_file ;
	
	newStr:= "__" + outFile + "\n" + "_lemma	_traduzione"
	
	for z:=0; z < len(dictLemmaTran); z++ {
		newStr +=  "\n" + dictLemmaTran[z].dL_lemma + " "  + dictLemmaTran[z].dL_tran 
	}
	//-----------		
	f, err := os.Create( outFile )
	check(err)
	defer f.Close();
	_, err = f.WriteString( newStr )
	check(err)
	f.Sync()
	
} // end of rewrite_wordDict_file

//---------------------------

func rewrite_rowDict_file() {

	outFile := dictionaryFolder  +  string(os.PathSeparator) + outRowDict_file;	 
	newStr := ""
	nout:=0  
	for z:=0; z < len( inputTextRowSlice); z++ {
		rtran := inputTextRowSlice[z].tran1
		if rtran != "" {		
			newStr += strconv.Itoa(z) +  "; " + rtran + "\n"  
			nout++
		}	
	}  
	fmt.Println("wrote ", nout , " lines on ", outFile )  
	//---		
	f, err := os.Create( outFile )
	check(err)
	defer f.Close();
	_, err = f.WriteString( newStr )
	check(err)
	f.Sync()		

} // end of rewrite_rowDict_file

//----------------------------------------
func console( str1 string) {
	go_exec_js_function( "js_go_console", str1 ) 	
}
//-----------------------------------------------