"use strict";
/*  
Words By Frequence: A tool to practice language comprehension
Antonio Cigna 2023
license MIT: you can share and modify the software, but you must include the license file 
*/
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */
//----------------------------------------------
// part 1/2
//-------------------------------------------- 
//console.log("file script loaded"); 
//------------------------
const wSep = "§";
const endOfLine = ";;\n"; 
let ele_allowWordTranslation= document.getElementById("id_allowWordTranslation"); 
let ele_wordsToTranslate 	= document.getElementById("id_words_to_translate");
let ele_wordsTranslated  	= document.getElementById("id_words_translated"  );
let ele_wordListDisplay  	= document.getElementById("id_wordListDisplay"   );
let ele_wordList = document.getElementById("id_wordList1");
//let ele_word     = document.getElementById("id_word"      );
//let ele_wRowList = document.getElementById("id_wRowList1");
//let ele_wordLisH = document.getElementById("id_wordListH");

let page01pre = document.getElementById("id_page01pre");
let page02_1pre = document.getElementById("id_page02_1pre");
let page02_2pre = document.getElementById("id_page02_2pre");
//let page03pre   = document.getElementById("id_page03pre");
//let page2       = document.getElementById("page2");
let maxNumRow = 100;
let wordToStudy_list ;

let prev_voice_ix        =  ""; 	
let	prev_voiceLang2      =  ""; 		
let	prev_voiceLangRegion =  "";  
let	prev_voiceName       =  ""; 
let listaInputFile   =""; 
let prevRunListFile  = ""
let lastRunLanguage  = "" 
const wordTTEnd     = ";:"
const wordTTBegin   = ";"
const wordSepEndBeg = wordTTEnd + wordTTBegin
//-------
let rowToStudy_list; 
let ele_toTranslate_textarea 	= document.getElementById("txt_pagOrig");  
let ele_translated_textarea  	= document.getElementById("txt_pagTrad"  );
let sw_newRowTranWritten = false;   // when true new translations  cannot  be asked 
 
//----------------
let sw_newWordTranWritten = false;   // when true new translations  cannot  be asked 
  
let newTran;  // is an array with the same length as wordToStudy_list, when the element is = true  then a new translated word has been written   
let newRowTran;
let sw_firstDictLine_already_existed = false; 
//console.log("window dimensions = w=" , window.innerWidth, "  h=", window.innerHeight);   
//console.log(" javascript " + screen.width + " x " + screen.height);
//---------------------------------------
let ele_where = document.getElementById("id_where");
let ele_bar   =  document.getElementById("id_progrBar");
let ele_bar2  =  document.getElementById("id_progrBar2");
//------------------
function js_go_updateStatistics(data) {
	// triggered by go func buildStatistics()
    document.getElementById("id_frequenze").innerHTML = data;
}

//---------------------------------------------------------
function onclick_require_mostFreqWordList() {

	ele_wordList.innerHTML = "";
	//ele_wRowList.innerHTML = "";
    //ele_word.innerHTML     = ""; 	 	
	//ele_wordLisH.style.display = "none"; 
	
	var sNumWords = document.getElementById("id_inpMaxNumWords").value;
    var sFromWord = document.getElementById("id_inpBegFreqWList").value;
    var fromWord = 0,
        numWords = 0;
    try {
        fromWord = parseInt(sFromWord);
    } catch (err) {}
    try {
        numWords = parseInt(sNumWords);
    } catch (err) {}
    if (fromWord < 2) {
        fromWord = 0;
    }

    go_passToJs_wordList(fromWord, numWords, "js_go_showWordList"); // ask 'go' to give wordlist by js_... function  

} // end of onclick_require_mostFreqWordListt

//------------------------------------------
function js_go_console( str1 ) {
	//console.log( str1 )	
} 

//------------------------------------
function js_go_showWordList(wordListStr) {
	
    // triggered by go func (  go_passToJs_wordList )
    if (wordListStr == undefined) {
        console.log("js_showWordList: parameter is undefined");
        return;
    }
    if (wordListStr == "") {
        console.log("js_showWordList: parameter is empty");
        return;
    }	
	var word2, ixUnW2, totRow2, wLemmaList, wTranList;
	
    var wordToStudy_listStr = wordListStr.split( endOfLine );	
	
	wordToStudy_list = []
	
	for (var z=0; z < wordToStudy_listStr.length; z++) {			
		
		if (wordToStudy_listStr[z].trim() == "") continue
		
		[word2, ixUnW2, totRow2, wLemmaList, wTranList] = getFieldsFromWordToStudy( wordToStudy_listStr[z],"1wordToStudy_"+z ); 	
		if (word2 == "") continue
		
		wordToStudy_list.push(  [word2, ixUnW2, totRow2, wLemmaList, wTranList] ); 		  // string, int, int, [str], [str]	
		
	}
	
	newTran = [];
	for (var z=0; z < wordToStudy_list.length; z++) {			
		newTran.push( 0 )
	}

	fun_showWordList("3") 
	
} // end of js_go_showWordList

//----------------
function getFieldsFromWordToStudy(  ww , where="") {
		
		           //  xWordF.word + "," + strconv.Itoa(xWordF.ixUnW) + "," + strconv.Itoa(xWordF.totRow)  + ";[" +xWordF.wLemmaL + "];[" + xWordF.wTranL) + "];"
		var ww0 = ww
		if (ww=="") { return ["",null,null,null,null]}
		//if (ww.indexOf("]") >0) { ww = (ww+";").replaceAll(";[",";").replaceAll("];",";")   }
		var piece;
		try{
			piece = ww.split(";")	
		} catch(e) {
			console.log("getFieldsFromWordToStudy( ww=" +  ww + "<==  ww0=", ww0) 		
		}
				
		return [ piece[0], piece[1], piece[2],  piece[3].split( wSep ) , piece[4].split( wSep ) ] ;
	
}
//------------------------------------
function fun_showWordList(wh, ix1=-1) {	
	
	var numNoTran = -1 
	var word2, ixUnW2, totRow2, wLemmaList, wTranList 
	var words_to_translate_str = wordTTBegin   //  ; 
	
	for (var z=0; z < wordToStudy_list.length; z++) {			
		
		[word2, ixUnW2, totRow2, wLemmaList, wTranList] = wordToStudy_list[z]; 	
		
		for(var f = 0; f < wLemmaList.length; f++) {	
			if (wTranList[f] == "") {			
				numNoTran++			
				words_to_translate_str += z + ";" + ixUnW2 + ";" + f + "; " +wLemmaList[f] + wordSepEndBeg;  // ;,;    // blank dopo ; prima di wLemma (serve per evitare problemi google)
			}
		}
	}
	
	if (numNoTran < 1) {		
		showWordsAndTranButton("2")
		return
	}	
	//console.log("X fun_showWordList(", wh, ")  words_to_translate_str =\n", words_to_translate_str)	
		
	ele_wordsToTranslate.value = words_to_translate_str; //  .replaceAll("\n"," "); 
	ele_wordsTranslated.value = ""; 
	onclick_jumpFromToPage( page01pre,0,page02_1pre);  
	

} // end of fun_showWordList
//------------------------------

function showWordsAndTranButton(wh) {
	//console.log(" showWordsAndTranButton(", wh, ") ")
	
	var showList = '' + 
			'<table style="border:0px solid black;width:95%;"  > \n' +
			'	<thead style="z-index:5;padding: 0 1em;">   \n' +   
			'		<tr><th class="righe1">n.</th><th class="right1">n.frasi</th><th  class="center">Word</th><th  class="right1">Lemma</th><th class="left1">Translation</th></tr> \n' +
			'	</thead> \n' +
			'	<tbody> \n' ; 		
	
    var word1, ix1, nrow, wLemma1;
	var riga;
	
	var wordOrig2, wordTran2;
	var wLemmaList, wTranList 
	
	var wordTran = ""; 
	var wLemma3, wTran3;
	var nSpanV, spanV;
	
	var clas1;
	var swP = false
	var hig=1
    for (var i = 0; i < wordToStudy_list.length; i++) {
		
		[word1, ix1, nrow, wLemmaList, wTranList] = wordToStudy_list[i]; 
		word1 = word1.trim(); 
        if (ix1 == undefined) {
            continue;
        }  
		if (parseInt(ix1) < 0) {continue}
		
		nSpanV =  wLemmaList.length
		
		for(var f = 0 ; f < wLemmaList.length; f++) {		
			hig = 1.2* wLemmaList.length 
			if (f==0) {	
				if (swP) { swP=false; clas1="pari"; } else { swP=true; clas1="dispari"}  
				spanV = ""				
				if (nSpanV > 1) {spanV= 'rowspan="' + nSpanV + '"';} 
				riga = '<tr class="' + clas1 + '">' + 
					'<td class="right hpad middle" style="width:5%;">' + ix1 + '</td>' + 
					'<td class="right middle"  style="width:5%;">' + nrow + '</td>' + 				
					'<td class="center hpad top" style="width:30%;height:100%;vertical-align:middle;" ' + spanV + ' >' +
					'  <button class="butt_w1" style="height:100%; vertical-align:middle;color:blue; font-weight:bold; font-size:1.0em;height:' + hig +'em;" onclick="onclick_wordByIndex(' + ix1 + ')">' + word1 + '</button>' +
					'</td>' ; 
			} else {
				riga = '<tr class="' + clas1 + '">' +  
					'<td class="right hpad middle" style="width:5%;">' + '</td>' +
					'<td class="right middle"  style="width:5%;">' + '</td>'  ;  					 				
					//'<td class="center hpad top" style="width:30%;">' +	'</td>' ; 
			} 
			riga += '<td  class="right1 hpad middle" style="width:30%;">' + 
						wLemmaList[f] + 
				'</td>' + 
				'<td class="left1 hpad middle" style="width:30%;">' +
					'<span class="tranTip hpad middle left1">' +
						'  <span class="tranTTxt left1" style="width:100%;">' + 
						wTranList[f] + 
						'</span>' +
					'</span>' +
				'</td>' + 
				'</tr> \n' ;   		
			showList    += riga + "\n";	
		}	
		
    }
	//---------------------------------------------------
	
	showList += '   </tbody>  \n' +
		'</table> \n'; 	
    ele_wordList.innerHTML = showList;
	
	onclick_jumpFromToPage( page01pre,page02_1pre, page02_2pre);  

} // end of showWordsAndTranButton

//-------------------------------------------------
function writeLanguageChoise() {
	//---------------------------------------------------
	// triggered by onclick_tts_get_oneLangVoice(this1) 
	
	//console.log("writeLanguageChoise()"); 
	
	var langRow = ""; 
	if ( isVoiceSelected ) {		
		langRow += selected_voice_ix + "," + selected_voiceLang2 + "," + selected_voiceLangRegion + "," +  selected_voiceName;
	}
	// langRow += "<file>" + prevRunListFile
	
	if (langRow == "") return
	if (langRow == lastRunLanguage) return
	
	console.log(" write file language " + langRow); 
	
	js_go_ready( langRow);  
	
	go_write_lang_dictionary(   "language="  + langRow );  
	
} // end of writeLanguageChoise
//--------------------------------------------
/***
function TOGLIwrite_lemma_tran_dictionary() {
	
	let word1, ix1, nrow, wLemma1, wordTran;
	var wLemmaList, wTranList;
	var newTranWord=0;
	var listNewTranWords = "";
	
    for (var i = 0; i < wordToStudy_list.length; i++) {
		
		[word1, ix1, nrow, wLemmaList, wTranList] = wordToStudy_list[i]; 
		word1 = word1.trim(); 
		if (ix1 == undefined) {
            continue;
        }  		
		if (ix1 < 0) continue; 
		
		if (newTran[i]==1) {
			newTranWord++; 	
			for( m=0; m < len(wlemmaList); m++ { 			
				listNewTranWords += "\n" + wLemmaList[m] + "\t" + wTranList[m] 
			}
		}
    }
	
	go_write_lemmaTran_dictionary(  listNewTranWords.substring(1)  ); 
	
} // end of write_lemma_tran_dictionary
****/
//--------------------------------------------------
function write_word_dictionary() {
	//console.log("write word dictionary()")
	let word1, ix1, nrow, wLemma1, wordTran;
	var wLemmaList, wTranList;
	var newTranWord=0;
	var listNewTranWords = "";
	
    for (var i = 0; i < wordToStudy_list.length; i++) {
		
		[word1, ix1, nrow, wLemmaList, wTranList] = wordToStudy_list[i]; 
		word1 = word1.trim(); 
		if (ix1 == undefined) {
            continue;
        }  		
		if (ix1 < 0) continue; 
		
		if (newTran[i]==1) {
			newTranWord++; 	
			listNewTranWords += "\n" + word1 + ";" + ix1 + ";" + wLemmaList.join( wSep ) + ";" + wTranList.join( wSep )  ;   // new line for dictionary 			
		}
    }
	
	console.log("X??anto2 write word dictionary() listNewTranWords =\n", listNewTranWords.substring(1) );
	
	go_write_word_dictionary(  listNewTranWords.substring(1)  ); 
	
} // end of write_word_dictionary

//---------------------------------------------------------

function onclick_require_prefixWordList() {
	 
	ele_wordList.innerHTML = "";
	//ele_wRowList.innerHTML = "";
    //ele_word.innerHTML     = ""; 	 
	//ele_wordLisH.style.display = "none";
    var sNumWords = document.getElementById("id_inpMaxNumWords").value;
    var wordPrefix = document.getElementById("id_inpPref").value.trim();   
	

	var numWords=0; 
    try {
        numWords = parseInt(sNumWords);
    } catch (err) {
		ele_wordList.innerHTML = '<span style="color:red;">errore numWords non numerico =>' + numWords +    '<== sNumwords=' + sNumWords + '<==  </span>';
		return;
	}
	if (numWords < 1) {
		ele_wordList.innerHTML = '<span style="color:red;">massimo numero di parole minore di 1</span>';
		return; 
	}	
	if (wordPrefix == "") {
		ele_wordList.innerHTML = '<span style="color:red;">manca il prefisso</span>';
		return;
	}	
	
    go_passToJs_prefixWordList(numWords, wordPrefix, "js_go_showPrefixWordList"); // ask 'go' to give wordlist by js_... function  
	
} // end of onclick_require_prefixWordList

//-------------

//------------------------------------
function js_go_showPrefixWordList(wordListStr) {
    // triggered by go func  (go_passToJs_prefixWordList)
	//console.log( "js_go_showPrefixWordList(wordListStr = " + wordListStr)
	
	if (wordListStr.substring(0,5) == "NONE,") {
			document.getElementById("id_inpPref_msgWord").innerHTML = wordListStr.substring(5) 
			document.getElementById("id_inpPref_msg").style.display = "block"
			document.getElementById("id_page01pre").style.display = "flex"; 
		return
	}
	document.getElementById("id_inpPref_msg").style.display = "none"
	onclick_jumpFromToPage( page01pre,0, page02_1pre);  
	
	js_go_showWordList(wordListStr);

} // end of js_go_showPrefixWordList
//------------------------------
function onclick_require_lemmaWordList() {
	
	ele_wordList.innerHTML = "";
	
    var aLemma = document.getElementById("id_inpLemma").value.trim();    
	if (aLemma == "") {
		ele_wordList.innerHTML = '<span style="color:red;">manca il lemma</span>';
		return;
	}	
	page01pre.style.display = "none"; 
	
	go_passToJs_lemmaWordList(aLemma, "js_go_showLemmaWordList"); // ask 'go' to give wordlist by js_... function  

}
//------------------------------------
function js_go_showLemmaWordList(wordListStr) {
	
	//console.log("js_go_showLemmaWordList(wordListStr=" + wordListStr)
	
	if (wordListStr.substring(0,5) == "NONE,") {
		document.getElementById("id_inpLemma_msgWord").innerHTML = wordListStr.substring(5) 
		document.getElementById("id_inpLemma_msg").style.display = "block"			
		document.getElementById("id_page01pre").style.display = "flex"; 
		return
	}
	document.getElementById("id_inpLemma_msg").style.display = "none"
	onclick_jumpFromToPage( page01pre,0, page02_1pre);  
	
	js_go_showWordList(wordListStr);

} // end of js_go_showLemmaWordList

//---------------------------------------------------------
function onclick_require_rowListWithThisWord() {
	
	ele_wordList.innerHTML = "";
	//ele_wRowList.innerHTML = "";
    //ele_word.innerHTML     = ""; 	 	
	//ele_wordLisH.style.display = "none";
	//console.log('document.getElementById("id_inpWordFra") =' , document.getElementById("id_inpWordFra").outerHTML) 
    var aWord     = document.getElementById("id_inpWordFra").value.trim();    
	if (aWord == "") {
		ele_wordList.innerHTML = '<span style="color:red;">manca la parola da cercare</span>';
		return;
	}	
	page01pre.style.display = "none"; 
	go_passToJs_thisWordRowList(aWord, maxNumRow, "js_go_showWordRowList"); 
		
} // end of onclick_require_rowListWithThisWord

//---------------------------------------------------------
function onclick_require_rowList() {
	
	ele_wordList.innerHTML = "";
	//ele_wRowList.innerHTML = "";
    //ele_word.innerHTML     = ""; 	 	
	
    var sNumRows   = document.getElementById("id_inpNumRow").value.trim();    
	var sInpBegRow = document.getElementById("id_inpBegRow").value.trim();    
    var numRows=0; 
	var inpBegRow=0;
    try {
        numRows = parseInt(sNumRows);
    } catch (err) {}
	
	try {
        inpBegRow = parseInt(sInpBegRow);
    } catch (err) {}
	
	
	//console.log("onclick_require_rowList() ", "  sNumRows=", sNumRows, " sInpBegRow=" , sInpBegRow , " XXX numRows=", numRows, " inpBegRow=" , inpBegRow) 
	
	page01pre.style.display = "none"; 
	document.getElementById("id_headWord").innerHTML = ""; //head1; 
	go_passToJs_rowList(inpBegRow, numRows, "js_go_rowList"); 
		
} // end of onclick_require_rowList

//-------------------------------
function onclick_wordByIndex(sIxWord) {
    // triggered by clicking on a word  
 	
    var ixWord = 0;
    try {
        ixWord = parseInt(sIxWord);
    } catch (err) {}
	
    go_passToJs_getWordByIndex(ixWord, maxNumRow,"js_go_showWordRowList"); // ask 'go' to give the rows of the word  by the go function js_go...  

} // end of onclick_wordByIndex
//-------------------------
function firstUpper(str1) {	
	return str1.substring(0,1).toUpperCase() + str1.substring(1).toLowerCase(); 
}
//-------------------
function checkUpper( thisWord, thisListRow) {
	/* if the word with the first letter capitalized 
	 is found in the rows but not at the beginning of the row 
	 then probably normally is the correct way to write it (eg. a Person Name)
	*/ 
	var upperThisW = " " + firstUpper(thisWord);  
	var righe = thisListRow.split(";;"); 
	for(var z1=0; z1 < righe.length; z1++)  {
		var riga = righe[z1].trim()
		if (riga.indexOf( upperThisW ) > 0 ) return true; 
	}  	
	return false;  
}
//---------------
function js_go_showWordRowList(inpstr) {

	// triggered by go ( bild go_passToJs_getWordByIndex )
	
    if (inpstr == undefined) {
		//console.log("js_go_showWordRowList() 1 return inpstr undefined ");  
        return;
    }
    if (inpstr == "") {		
		//console.log("js_go_showWordRowList() 2 return inpstr vuoto");  
        return;
    }
	
	if (inpstr.substring(0,5) == "NONE,") {
		document.getElementById("id_inpWordFra_msgWord").innerHTML = inpstr.substring(5) ;
		document.getElementById("id_inpWordFra_msg").style.display = "block";
		document.getElementById("id_page01pre").style.display = "flex"; 
		return
	}	
	document.getElementById("id_inpWordFra_msg").style.display = "none";

    var k = inpstr.indexOf("<br>");
	
	if (k < 0) {
		//console.log("js_go_showWordRowList() 3 return k=" + k );  
        return;
    }	
    var thisWordList    = inpstr.substring(0, k);
	var thisListRow = inpstr.substring(k + 4);
	
	var word3, ixUnW3, totRow3, wLemma3, wTran3;
	
	
	var aWord = thisWordList.split(endOfLine); 
	var col0 , Xwor1, Xix, Xf,Xlem,Xtran ;
	var thisWord = ""; var aLine 
	
	
	var numFilled=0
	for(var z=0; z < aWord.length;z++) {		
		if (aWord[z] == "" ) continue	
		col0 = aWord[z].split(";")
		if (col0.length < 5) continue	
		[Xwor1, Xix, Xf,Xlem,Xtran] = col0	
		if (Xwor1 == "") continue
		if (thisWord == "") thisWord = Xwor1 
		numFilled++
	}
	var swOnlyOneWord=false
	var swUpper = checkUpper( thisWord, thisListRow); 	
	
	var table1 = '<table style="font-size:0.8em;"> \n' ;
	var jLast = aWord.length-1;
	var swFirst=true
	for(var z=0; z < aWord.length;z++) {
		//console.log("z=", z , aWord[z] )
		if (aWord[z] == "" ) continue	
		col0 = aWord[z].split(";")
		if (col0.length < 5) continue	
		[Xwor1, Xix, Xf,Xlem,Xtran] = col0
		
		var upLem = Xlem; var upTran = Xtran
		if (swUpper) { upLem = firstUpper(Xlem); upTran = firstUpper(Xtran); }
	
		if (Xwor1 == "") continue
		if (swFirst) {
			swFirst = false; 
			thisWord = Xwor1
			if (numFilled == 1) {  // solo una parola 
				if (Xwor1 == Xlem) {
					swOnlyOneWord=true
					table1 += '<tr>' + 
						'<td style="color:blue;vertical-align:bottom;">'       + upLem  + '</td>' +
						'<td style="vertical-align:bottom;padding-left:1em;">' + upTran + '</td>' + 
						'</tr>\n';  
					break; 
				}
			} 
		}		
		table1 += '<tr>' + 
			'<td style="width:4em;"></td>' +
			'<td style="color:blue;vertical-align:bottom;">'       + upLem  + '</td>' +
			'<td style="vertical-align:bottom;padding-left:1em;">' + upTran + '</td>' + 
			'</tr>\n';  
	}	
	
	//console.log("swOnlyOneWord=" , swOnlyOneWord);
	
	table1 += '</table>\n' ;
	
	
	var upThis = thisWord; 
	
	if (swUpper) { upThis = firstUpper(thisWord); }
			
	var head1 = '<div class="centerXY" style="width:100%;">' + 	'<div style="text-align:left;">' ;
	
	if (swOnlyOneWord == false) { head1 +=	'<span style="color:blue;">' + upThis + '</span> \n' ; }
	head1 +=  table1 +'</div></div>\n'; 	
	
	//console.log("head1=\n" + head1) 	
	
	word_to_underline = thisWord; // thisWord  // used by 'tts_5_fun_build_all_clip()' function in 'lbl_script_5_tts_otherFuns.js' file  
	
	document.getElementById("id_headWord").innerHTML = head1; 
	
	onclick_jumpFromToPage( page02_1pre,page02_2pre, page1);  //   
	
	js_go_rowList( thisListRow )   // nuovo 2 ottobre 
	
	
} // end of js_go_showWordRowList
//--------------------------------------------

function js_go_rowList( inpstr ) {
	
	// triggered by go ( go_passToJs_rowList )
	
    if (inpstr == undefined) {
		console.log("js_go_rowList() 1 return inpstr undefined ");  
        return;
    }
	
    if (inpstr == "") {		
		console.log("js_go_rowList() 2 return inpstr vuoto");  
        return;
    }
	
	rowToStudy_list =  inpstr.split("<br>");	
	
	newRowTran = [];
	
	for (var z=0; z < rowToStudy_list.length; z++) {
		
		newRowTran.push( 0 )
	}
	
		
	fun_showRowList("3") 
	
} // end of js_go_rowList
//-------------------

function fun_showRowList( wh ) {
	
	//console.log(" fun_showRowList(", wh,")")
	
	var numRowNoTran = 0 
	var rows_to_translate_str = "";  
	
	var nfile,ixRow,p3,rowS, tranS, nfileS, ixRowS, oT; 
	
	//console.log(" fun_showRowList(", wh,")",  "  1  length=", rowToStudy_list.length )
	
	for (var z=0; z < rowToStudy_list.length; z++) {		
		/*
		;;0;;2;; Erstes Kapitel;; Primo Capitolo 
		;;0;;3;; 
		;;0;;4;; Gustav Aschenbach oder von Aschenbach, wie seit seinem fuenfzigsten;; Gustav Aschenbach o von Aschenbach, come ha fatto fin dai cinquant'anni
		;;0;;5;; Geburtstag amtlich sein Name lautete, hatte an einem;;Il suo compleanno ufficiale cadeva l'una		
		*/
		
		oT = ("" + rowToStudy_list[z]).trim();	
		
		if (oT == "") {  continue;}
		if (oT.substring(0,2) != ";;") { continue; }
		[nfileS,ixRowS, rowS, tranS] =  oT.substring(2).split(";;") ;  // eg. ;;0;2;; Primo capitolo	
		
		

		rowS  = rowS.trim()
		tranS = tranS.trim()
		
		if (rowS == "") {continue}
		if (tranS == "") {
			numRowNoTran++
			rows_to_translate_str += z + ";;" + ixRowS + ";; " + rowS + "\n";   //  lascia lo spazio prima di rowS (evita problemi nelle traduzione con google 
			//console.log("\t fun_showRowList() 2.2 rows_to_translate_str = ",  z + ";" + ixRowS + ";" + rowS + "<== MANCA TRANS XXXXXXXX\n" )
		} else {
			//console.log("\t fun_showRowList() 2.3 tranS=" + tranS + "<==  TROVATO ") 			
		}
	}
	//------------------
	
	if (sw_newWordTranWritten) {
		numRowNoTran = -1
		showRowsAndTranButton("1")
		document.getElementById("id_no_newTran").style.display = "block"
		return
	}	
	
	if (numRowNoTran < 1) {		
		showRowsAndTranButton("2")
		return
	}	
	
	ele_toTranslate_textarea.value = rows_to_translate_str;
	ele_translated_textarea.value = ""; 
	
	onclick_jumpFromToPage( page01pre,0,page1);   
	onclick_jumpFromToPage( page01pre,0,page1);   
	
} // end of fun_showRowList	

//-------------------------------------------------

function js_go_showReadFile( str1 ) {
	
	var j1 = str1.indexOf( "))" ); 
	var mainNum     = str1.substring(0,j1);
	var fileListStr = str1.substring(j1+2); 
	
	var numUniW, numTotW, numRow;
	[numUniW, numTotW, numRow] = mainNum.split(";")

	str1 = parseInt(numUniW).toLocaleString() + " parole diverse" + "<br>in totale " + parseInt(numTotW).toLocaleString() + " parole su un testo di " + parseInt(numRow).toLocaleString() + " righe"  
	
    var rows = fileListStr.split(";");
    var td1, td2;
    //var modelTR = document.getElementById("id_start_trModel").outerHTML;
	str1 += "<hr>"
	var str2 = '<table style="border:0px solid black">\n';
	//str2 += '<tr><th colspan="2">input</th></tr> \n' ;   	
    for (var i = 0; i < rows.length; i++) {
        if (rows[i] == "") continue;
        [td1, td2] = rows[i].split("<file>");			
		var k1= td2.lastIndexOf("\\")
		var k2= td2.lastIndexOf("/")	
		var k3 = Math.max(k1,k2) ;
		listaInputFile = td2.substring(k3+1).trim() + "," 
		str2 += '<tr><td>' + td2.substring(k3+1) + '</td>' +
			'<td>(' + parseInt(td1).toLocaleString() + " righe" + ')' + '</td></tr> \n' ;  
    }
	str2 += '</table>';
	
	var str0 = '<div style="border:1px solid black">';
	
	document.getElementById("id_inpFileList").innerHTML = str0 + str1 + ""+ str2 + "</div>";
	
}
//------------------------------------
function js_go_ready( prevRun) {
	
	var prevRunLanguage = prevRun.trim(); 
	if (prevRunLanguage != "") {
		sw_firstDictLine_already_existed = true; 
		lastRunLanguage = prevRunLanguage
		//console.log("language file has been read ==>" +  lastRunLanguage) 
	} 	
  
    document.getElementById("id_start001").style.display = "none";
    page01pre.style.display = "flex";
	
    document.getElementById("id_showButt").style.display = "block";
    document.getElementById("id_start_tab").style.display = "none";
	
	if (prevRunLanguage != "") { 
		lastRunLanguage = prevRunLanguage
		loadPrevLang( prevRunLanguage ) 
	}	else {
		fcommon_load_all_voices(); // at end calls tts_1_toBeRunAfterGotVoices()		
		// WARNING: the above function contains asynchronous code.  
		// 			Any statement after this line is executed immediately without waiting its end			
	}
	
}
//-------------------------------------

function onclick_show_or_hide_statistics() {
    var eleFreq   = document.getElementById("id_frequenze");
    var eleStFile = document.getElementById("id_start_tab");


    if (eleFreq.style.display == "block") {
        eleFreq.style.display   = "none";
        eleStFile.style.display = "none";
    } else {
        eleFreq.style.display   = "block";
        eleStFile.style.display = "block";
    }
} // end of onclick_require_statistics

//----------------------------------------------------

function evidenzia( unaparola, txtinp1) {
	
	unaparola = unaparola.toLowerCase().trim();
	var lenParola = unaparola.length; 
	var lowinp1 = txtinp1.toLowerCase() + "            ";
	var separator = " ;,:\"\'."  + '<>';
	var tabParo1 = []; var tabParo2 = []; 	
	var pre=0;	var x1=0; var pp; var nn=0; var i=0;
	
	//-------------
	for(i=0; i < lowinp1.length; i++) {
		pre = nn; 
		x1 = lowinp1.indexOf(unaparola,pre) ;		
		if (x1 < 0) {break;}
		pp=x1-1; nn = x1 + lenParola; 
		if (pp>=0) {
			var chPre = lowinp1.substr(pp,1);
			if 	(separator.indexOf(chPre) < 0) continue;
		}
		if (nn>=0) {			
			var chNn  = lowinp1.substr(nn,1);	
			if 	(separator.indexOf(chNn) < 0) continue;
		}
		tabParo1.push(pp); tabParo2.push(nn);
	}   
	var j1, j2=0; var jj;
	var newRow="";
	var lenrow = txtinp1.length;
	tabParo1.push(lenrow);
	tabParo2.push(0);
	
	for(var j=0; j < tabParo1.length; j++) {
		jj = j2;				
		if (jj > lenrow) break;
		j1 = tabParo1[j]; j2 = tabParo2[j];   
		newRow += txtinp1.substring(jj, j1) ;		
		if (j2 < 1) break;
		if (j2 < j1) continue;
		newRow += wBold_set( txtinp1.substring(j1, j2) );	
		
	}	
	return newRow;  
	//------------------------------
	function wBold_set( winp ) {
		//return "<b>" + winp + "</b>" ;
		return '<span class="wBold">' + winp + "</span>"; 
	}	
	
} // end of evidenzia 

//----------------------------------------------------
function onclick_jumpFromToPage( fromPage1, fromPage2, toPage, blockFlex = "flex") {
	//console.log("onclick_jumpFromToPage()" + "fromPage=", fromPage1,  " toPage=" , toPage, " blockFlex=", blockFlex);  	
	fromPage1.style.display = "none"; 
	if (fromPage2 != 0) {	fromPage2.style.display = "none"; }
	try {
		toPage.style.display = blockFlex;
	} catch(e1) {
		console.log("onclick_jumpFromToPage()" + " toPage=" , toPage);  
			console.log(e1);
	}
}

//----------------------------------------------------
function onclick_jumpFromTo1_2Page( fromPage1, fromPage2, toPage, toPage2, blockFlex = "flex") {
	
	fromPage1.style.display = "none"; 
	if (fromPage2 != 0) {	fromPage2.style.display = "none"; }
	
	if(ele_wordList.innerHTML == "") {
		try {
			toPage2.style.display = blockFlex;
		} catch(e1) {
			console.log("onclick_jumpFromToPage()" + " toPage=" , toPage2);  
			console.log(e1);
		}
		
	} else {	
		try {
			toPage.style.display = blockFlex;
		} catch(e1) {
			console.log("onclick_jumpFromToPage()" + " toPage=" , toPage);  
			console.log(e1);
		}
	}
}
//--------------------------------------------------

function onclick_copyTextAreaValue_to_clipboard( this1 ) {
	// copy textarea value to clipboard (from where you can paste)  
	this1.select();
	this1.setSelectionRange(0, 99999);
	navigator.clipboard.writeText(this1.value);  
}
//--------------------------------------------------------
function copyInnerHTML_to_clipboard( this1 , ele_textarea) {
	// copy innerHTML to textarea value and then ask to copy from that to clipboard (from where you can paste) 
	// textarea might be with display none  if you need 
	ele_textarea.value = this1.innerHTML.replaceAll("<br>","\n") ;
	onclick_copyTextAreaValue_to_clipboard( document.getElementById('myInput') );
}
//--------------------------------------

function onclick_showWordsButton() {
	//console.log("onclick_showWordsButton() ") 	
	/*
												 ele_wordsTranslated.value is filled manually ( ie. copied from google translator) 
	*/
	var wordTranList = ele_wordsTranslated.value.trim().split( wordTTEnd );    // 
		// words_to_translate_str += z + ";" + ixUnW2 + ";" + f + "; " +wLemmaList[f] + wordSepEndBeg  // ;,;    
	
	//console.log("X3 onclick_showWordsButton()  wordTranList=\n", wordTranList ) 	
	
	var lenTran =  wordTranList.length;	
	var wordTran
		
	var ixUnTrad, ixUnWtS;
	var lenW = wordToStudy_list.length;
	var word1, nrow, wLemma1, wtran; 
	var newTran_f = "";
	//------------------------------------------
	var wX, wT, ixz1,  ixz2, ixzNum   

	//-----------
	var wList;
	var sw_someTranMissing = false;  // sometimes the automatic translator does some mistakes 
	var wLemmaList, wTranList, newTranList ; 
	var numf=0
	//----------------------------
	for(var z=0; z < lenTran; z++) {
	
		wT = wordTranList[z].toLowerCase(); 	
		//                             z + ";" + ixUnW2 + ";" + f + "; " +wTran    ( soltanto UNA traduzione (quella del lemma num.f 
		if (wT == "") {continue;}
		if (wT.substring(0,1) != wordTTBegin) {continue}

		
		
		wList =  wT.substring(1).split(";") ;
		
		//console.log("X3.0 onclick_showWordsButton() z=",z, " wT=", wT , " XXX  wList=", wList) 
		
		if (wList.length < 4) { 
				//console.log("onclick_showWordsButton() errorT  entry z=" + z + " = " + wT ); 
				continue;
		}
		[ixzNum, ixUnTrad, numf, newTran_f] = wList ;              //   ix: translation word		 
	
		//ixzNum is the index of the word in wordToStudy_list
		
		[word1, ixUnWtS, nrow, wLemmaList, wTranList] = wordToStudy_list[ixzNum]; 
		
		//console.log("\n------------------------\nwordToStudy_list[ixzNum=", ixzNum,"]= ",  wordToStudy_list[ixzNum] , " ==> ", [word1, ixUnWtS, nrow, wLemmaList, wTranList] ) 
		//console.log(" wordTranList[z]=", wT, " ===> wList= [ixzNum, ixUnTrad, numf, newTran_f]=", [ixzNum, ixUnTrad, numf, newTran_f] ); 
		
		if ( parseInt(ixUnWtS) != parseInt(ixUnTrad)) {
			sw_someTranMissing= true;	
			console.log("onclick_showWordsButton() error4 entry z=" + z + " = " + wT  + "\n\t wordToStudy_list[ixzNum="+ ixzNum +"]=" +  wordToStudy_list[ixzNum] +  
				"\n\tixUnWtS=" + ixUnWtS + " ixUnTrad=" + ixUnTrad);	
			
			continue; 
		} 
		var numLemma = parseInt( numf ); // index of the lemma and its translation in the [lemmalist][tran list] in wordToStudy_list 
		newTran[ixzNum] = 1; 
		
		//console.log("anto newTran[ixzNum=" + ixzNum + "] = 1" ); 
		
		for(var h = 0 ; h < wLemmaList.length; h++) {	
			if (h == numLemma) {
				wTranList[h] = newTran_f.trim();
			} 
		}
		
		//wordToStudy_list[ixzNum] = [word1 , ixUnWtS, nrow, wLemmaList, newTranList.substring(1) ;   // update  element  
		
		wordToStudy_list[ixzNum][4] = wTranList;      
		
	}  // end of for(var z ...
	//--------------------------	
	
	if (sw_someTranMissing) {		
		//console.log("onclick_showWordsButton() return 1 sw_someTranMissing=true") 
		fun_showWordList("1")
		return;
	}		
	//console.log("onclick_showWordsButton() wordToStudy_list.length=" , wordToStudy_list.length)
	for (var i = 0; i < wordToStudy_list.length; i++) {
       
		[word1, ixUnWtS, nrow, wLemmaList, wTranList] = wordToStudy_list[i];  
		
		//console.log("X??anto3.1 onclick_showWordsButton() wordToStudy_list[]=" , wordToStudy_list[i], " XXXX " , [word1, ixUnWtS, nrow, wLemmaList, wTranList] )
		
		if (word1 == "") { continue; }
				
		for(var f = 0 ; f < wLemmaList.length; f++) {	
			if (wTranList[f] == "") {	
				sw_someTranMissing = true;  				
				fun_showWordList("2", i)
				return;		
			}
		}
	}	
	
	console.log("onclick_showWordsButton() write word dictionary ") 
	
	write_word_dictionary(); 
	
	showWordsAndTranButton("3");
	
} // end of onclick_showWordsButton()
//---------------------------


//------------------------
function extract_ix_word( i,wordOrig2 ) {
		// var wordOrig2 = wordOrigList[i].trim(); 		
		var pp= wordOrig2.indexOf(";"); 
		
		//console.log("antonio extract_ix_word( i=" + i + "  wordOrig2=" + wordOrig2 + " ==> pp=" + pp)  
		
		if (pp< 0) { return "";}
	
		var ix2 = wordOrig2.substring(0, pp); 
		var	ww2 = wordOrig2.substring(pp+1).trim(); 		
		
		//console.log("\t\t i=" + i + "   ix2=" + ix2 + "   ww2=" + ww2)  
		
		try{
			var ix3 = parseInt( ix2 );
			if (ix3 == i) return ww2;
			return ""; 	
		} catch(e1) {
			return "";			
		}
} // end of extract

//----------------------------------------------------
// set previous run voice
 
function loadPrevLang(prevLanguage) {
	
	// language=5,de,de-DE,Microsoft Stefan - German (Germany)   ( it's in the first line of dictionary) 
	//          0,1 ,2    ,3  
	var pvLang = prevLanguage.split(",") 
		
		
	prev_voice_ix        =  pvLang[0] ; 	
	prev_voiceLang2      =  pvLang[1] ; 		
	prev_voiceLangRegion =  pvLang[2] ;  
	prev_voiceName       =  pvLang[3] ; 
	 
	//console.log(" wordByFrequence.js loadPrevLang()" + " prev_voiceName = "+  prev_voiceName  );  
	
	fcommon_load_all_voices(); // at end calls tts_1_toBeRunAfterGotVoices()
	
	// WARNING: the above function contains asynchronous code.  
	// 			Any statement after this line is executed immediately without waiting its end

} // 
//---------------------------------
function js_go_setError(msg) {
	document.getElementById("id_startwait").innerHTML = msg; 	
}
//------------------------------
var numP=0
function whereIs(here) {
	//numP++
	
	//if (numP < 10) { console.log( "\whereIs(" + here) }
	
	if (here.substring(0,2) != "::") {	
		//ele_where.innerHTML = here ;
		return ;
	}
	
	var cols = here.split("::")
	//ele_where.innerHTML = cols[2];
	var perc=0;
	try{
		perc = parseInt( cols[1] )
		ele_bar.style.width = perc + "%";  
		ele_bar2.style.width = (100-perc) + "%";  
	} catch(e1) {
	}	
 	
	
} 
//-------------------------
function showProgress(perc0) {
	var perc=0;
	try{
		perc = parseInt( perc0 )
		ele_bar.style.width = perc + "%";  
		ele_bar2.style.width = (100-perc) + "%";  
	} catch(e1) {
	}		
}
//----------------------------------

function onclick_tts_seeWordsGO1(this1, numId00) {	

	//  attenzione numId è il numero progressivo ROW nella pagina del run corrente,  non è il numero reale row del testo  
	var eleTR = document.getElementById("idtr_" + numId00);  
	
	//console.log("onclick_tts_seeWordsGO1(this1," , numId00, ") ==> ", eleTR.outerHTML)
	
	var numIdRow = eleTR.children[ eleTR.children.length-1 ].innerHTML;    //  0_123   numberOfFile_num.row 
	
	var rr1 = numIdRow.split("_")
	var numId = parseInt(rr1[1]); 	
	var numIdOut = (""+numId00).trim();   
	
	
	
	var id_analWords = "idw_" + numId00;
	var ele_wordset = document.getElementById(id_analWords);   
	if (ele_wordset == false) {return}
	
	go_passToJs_rowWordList(numIdOut,numId, "js_go_rowWordList"); // ask 'go' to give wordlist by js_... function  
	
	
	ele_wordset.innerHTML = ""; 
	
	
} // end of onclick_tts_seeWordsGO1



//------------------------------------
function js_go_rowWordList(wordListStr) {
	
    // triggered by go func (  go_passToJs_wordList )
    if (wordListStr == undefined) {
        console.log("js_showWordList: parameter is undefined");
        return;
    }
    if (wordListStr == "") {
        console.log("js_showWordList: parameter is empty");
        return;
    }	

    var rowWordList = wordListStr.split(endOfLine);	
	
	//console.log("rowWordList=", rowWordList)
	
	var numId_0 = rowWordList[0].split(",");
	var numId = (""+numId_0[0]).trim();  	
	

	var anal_txt = ""; var anal_tts_txt=""; 
	var idc1 = "idc_"  + numId;
	var idtts= "idtts" + numId; 

	var anal_ele_idc   = document.getElementById(idc1 );		
	var anal_ele_idtts = document.getElementById(idtts);	
		
	if (anal_ele_idc) {
		anal_txt = anal_ele_idc.innerHTML;
		anal_tts_txt= anal_ele_idtts.innerHTML; 
	} else {
		return;
	}
	
	var eleTR = anal_ele_idtts.parentElement.parentElement.parentElement; 
	var trHeight = eleTR.offsetHeight; 	
	
	var id_analWords = "idw_" + numId;
	var ele_wordset = document.getElementById(id_analWords);   
	
	
	if (last_ele_analWords_id != "") {	
		// remove the previous 
		var last_ele_analWords = document.getElementById(last_ele_analWords_id);
		if (last_ele_analWords)  {
			
					
			last_ele_analWords.style.height = null;   				
			last_ele_analWords.innerHTML = "";  
			last_ele_analWords_tr.style.height = last_ele_analWords_height;	
			
				
			last_ele_analWords = null; 					
		}	
		if (id_analWords == last_ele_analWords_id) {  // if it's the same as the previous then  remove it  		
			last_ele_analWords = null; 	
			last_ele_analWords_id = "";
			return; 
		}	
		last_ele_analWords_id = "";
	}	
	
	var ixLastEle, table_txt
	[ ixLastEle, table_txt] = tts_3_spezzaRiga3( rowWordList.slice(1) )	 ;   
 	
	var divWord = "";
	
	divWord += table_txt;
	
	ele_wordset.innerHTML = divWord; 
	
	if (ixLastEle > 0) {
		var eleF = document.getElementById("wb1_0");
		var eleT = document.getElementById("wb2_" + ixLastEle );
		onclick_tts_word_arrowFromIx(eleF, 0,         true, false)
		onclick_tts_word_arrowToIx(  eleT, ixLastEle, true, false)
	}	
	
	var prevTR  = document.getElementById( "idtr_" + (numId-4) ); 
	if (prevTR) tts_5_fun_scroll_tr_toTop( prevTR ); 	// scroll 
		
	last_ele_analWords_id = id_analWords;
	last_ele_analWords_tr = eleTR; 
	last_ele_analWords_height = trHeight;  
	
} // end of js_go_showWordList

//------------------------------------
// ===================================================================
function tts_3_spezzaRiga3( rowWordList ) {
	
    var endix2 = -1;

    var listaParole = [];
    var listaParo_tts = [];	
    var listaParo_lemma = [];
    var listaParo_tran  = [];
	

    //console.log( list1.length + " " + list2.length); 


   // if (list2.length != list1.length) list2 = orig_riga2.split("§");
	var row1, k1,k2, col1; var part1;
	var xWord1;
	var listLemS, listTranS; 
	var listLem, listTran	
	
    for (var k = 0; k < rowWordList.length; k++) {
		row1 = (rowWordList[k]+";").replaceAll(";[",";").replaceAll("];",";")
		if (row1.trim()=="") continue; 
		
		//if (k==1) console.log("spezzaRiga3 k=" , k, " row=>" , row1); // spezzaRiga3 k= 6  row=> einem,14,2;[ein einem einer];[a uno uno]
		
		part1 = row1.split(";") 
		if (part1.length < 3) continue
		col1 = part1[0].split(",")
		xWord1 = col1[0];
		listLemS = part1[1]; 
		listTranS = part1[2]
		listLem = listLemS.split(   wSep ) ;   //  cambia separatore spazio con virgola 
		listTran = listTranS.split( wSep ) ;   //  
		
		//if (k==1) console.log("xWord1=", xWord1, " listLem=",  listLem, " trn=", listTran);  
		
		var strLT="";
		if (listLem.length == 1) {
			if (listLem[0] == xWord1) {
				strLT = listTran[0]
			} else {
				strLT = '<span style="color:blue;padding-right:0.5em;">' + listLem[0] + '</span>' + '<span>' + listTran[0] + '</span>' 	;				
			} 
		} else {
			strLT="<table>"
			for(var f=0; f < listLem.length; f++) {
				strLT += '<tr><td style="color:blue;padding-right:0.5em;">' + listLem[f] + '</td>' + '<td>' + listTran[f] + '</td></tr>' 			
			}		
			strLT += '</table>'; 
		}
		
		listaParole.push(   xWord1 ) ;
        listaParo_tts.push( xWord1 ) ;
		listaParo_lemma.push( strLT );		
    }
    var parola1, paro_tts, paro_lemma, paro_tran;

    var frase_showTxt = '<table style="border:0px solid red;width:100%;margin-top:1em;"> \n';

    for (let z3 = 0; z3 < listaParole.length; z3++) {
        parola1    = listaParole[z3];
        paro_tts   = listaParo_tts[z3];
		paro_lemma = listaParo_lemma[z3];
		paro_tran  = ""
        /**
		paro_tran  = listaParo_tran[z3];		
		if (paro_lemma == parola1) {  
			paro_lemma = ""
		} else { 
			paro_lemma += "<br>"
		}
		**/
        let rowclip = word_tr_allclip.replaceAll("§1§", z3).replaceAll("§4txt§", parola1).replaceAll("§ttsWtxt§", paro_tts). replaceAll("§7txt§", paro_lemma).replaceAll( "§6txt§", paro_tran)
        frase_showTxt += rowclip + "\n";
    } // end of for z3
	var last1 = listaParole.length - 1 
	
    return [ last1, frase_showTxt += '</table>\n' ];

} //  end of  spezzaRiga3()

//====================


function onclick_FR_tts_getInput(elepage) {

  if (fr_tts_1_join_orig_trad() < 0) {
	  return;
  }

  var elepage1 = document.getElementById("page1");
  var elepage2 = document.getElementById("page2");
  if (elepage == elepage1) {
	  elepage2.style.display = "block";
  } else {
	  elepage1.style.display = "block";
  }
  elepage.style.display = "none";
}
//------------------------------------  

function fr_tts_1_join_orig_trad() {
	document.getElementById("id_msg16").innerHTML = "";

	sw_translation_not_wanted = false;

	var msgerr0 = "";
	var msgerr1 = fr_tts_1_get_orig_subtitle2(); // get orig. text /srt
	var msgerr2 = fr_tts_1_get_tran_subtitle2(msgerr1); // get tran. text/srt	

	msgerr0 += msgerr1 + msgerr2;
	var msgerr3 = "";

	msgerr0 += msgerr3;

	if (msgerr0 != "") {
		tts_1_putMsgerr(msgerr0);
		document.getElementById("id_msg16").style.color = "red";
		return -1;
	}
	document.getElementById("id_msg16").style.color = null;

	tts_9_toBeRunAfterGotVoicesPLAYER(); 

	return 0;

} // end of tts_1_join_orig_trad()

//----------------------

//--------------------------------------------------
 function fr_tts_1_get_orig_subtitle2() {
     
      var msgerr1 = "";
    
      builder_orig_subtitles_string = document.getElementById("txt_pagOrig").value.trim();
	  
      if (builder_orig_subtitles_string != "") {
          sw_inp_sub_orig_builder = true;
      } else {
          sw_inp_sub_orig_builder = false;
          msgerr1 += "<br>" + tts_1_getMsgId("m132"); //  ma22 the source language subtitle file  has not been read or is empty" ;         
      }
	  inp_row_orig = builder_orig_subtitles_string.split("\n") ;
	  inp_row_orig.push("");    
	  numOrig = inp_row_orig.length;
	
      return msgerr1;

  } // end of get_orig_subtitle2()
  //--------------------------------------------------

  function fr_tts_1_get_tran_subtitle2(msgerrOrig) {
     
      var msgerr1 = "";

      builder_tran_subtitles_string = document.getElementById("txt_pagTrad").value.trim();
	  
      sw_inp_sub_tran_builder = false;
      if (builder_tran_subtitles_string != "") {
          sw_inp_sub_tran_builder = true;
      } else {
          sw_inp_sub_tran_builder = false;
          if (sw_translation_not_wanted == false) {
              msgerr1 += "<br>" + tts_1_getMsgId("m133"); //    translated subfile missing     					
              if (msgerrOrig == "") { // only if original srt is Ok  
                  msgerr1 += "<br>" + tts_1_getMsgId("m134").replace("§...§", TRANSLATION_NOT_WANTED); // if there is no translation
			  }
          }
      }
	  inp_row_tran = builder_tran_subtitles_string.split("\n");
	  inp_row_tran.push(""); 
	  numTran = inp_row_tran.length;  
	  
      return msgerr1;

  } // end of tts_1_get_tran_subtitle2()

//--------------------------
function replaceSepar( wT1 ) {	
	/**
	1;;1374;;sie zum zweiten Male jaeh zu verlassen gezwungen war, so hatte er sie
	1, 1374, e fu costretto a lasciarla per la seconda volta, l'ebbe
	**/
	var k1,k2,k3,kx1,kx2, kx10,kx20, num1,num2,new_wT;
	
	k1 = wT1.indexOf(";;"); if (k1 < 0) k1=99999
	k2 = wT1.indexOf(";" ); if (k2 < 0) k2=99999 
	k3 = wT1.indexOf("," ); if (k3 < 0) k3=99999
	kx1 = Math.min(k1,k2,k3)
	if (kx1 > 14) return wT1
	num1 = wT1.substring(0,kx1).trim()
	kx10 = kx1+1
	if (wT1.substr(k1,2) == ";;") kx10 = kx1+2  
	//console.log("??anto replace... k1,k2,k3=",k1,k2,k3, "  kx1=", kx1, "  kx10=", kx10, " num1=" , num1, " da kx2=" + wT1.substring(kx10) )
	
	k1 = wT1.indexOf(";;", kx10); if (k1 < 0) k1=99999
	k2 = wT1.indexOf(";",  kx10); if (k2 < 0) k2=99999 
	k3 = wT1.indexOf(",",  kx10); if (k3 < 0) k3=99999
	kx2 = Math.min(k1,k2,k3)	
	if (kx1 > 8) return wT1;
	
	num2 = wT1.substring(kx10, kx2).trim() 
	kx20 = kx2+1
	if (wT1.substr(k2,2) == ";;") kx20 = kx2+2  
	
	//console.log("??anto replace2... k1,k2,k3=",k1,k2,k3, "  kx2=", kx2, "  kx20=", kx20, " num2=" , num2, " da kx2=" + wT1.substring(kx20) )
	
	var rest = wT1.substring(kx20).trim(); 
	new_wT = num1 + ";;" + num2 + ";;" + rest;
	try {
		var num1Nu = parseInt(num1);
		var num2Nu = parseInt(num2);
	} catch(e) {
		return wT1; 		
	} 
	
	//console.log("??anto replace " + wT1 + "\n\t\t new " + new_wT);   
	
	return new_wT; 
	
} 
//--------------------------------------

function onclick_showRowsButton() {
		
		//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX    NUOVA TRATTAMENTO         ROWS            XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
	
	//console.log("objOrig.value=", objOrig.value)	
	//console.log("objTran.value=", objTran.value)	
	/***	
	objOrig.value= 
	;;0;2;; Erstes Kapitel
	;;0;3;; 
	;;0;4;; Gustav Aschenbach oder von Aschenbach, wie seit seinem fuenfzigsten
	;;0;5;; Geburtstag amtlich sein Name lautete, hatte an einem

	objTran.value=
	;;0;2;; Primo capitolo
	;;0;3;;
	;;0;4;; Gustav Aschenbach o von Aschenbach, come ha fatto fin dai cinquant'anni
	;;0;5;; Il suo compleanno ufficiale cadeva l'una	
	***/
	
	var rowTranList = ele_translated_textarea.value.trim().split( "\n" );      	 
	
	var lenTran = rowTranList.length;	
	
	var lenW    = rowToStudy_list.length;
	
	var rowTran
	var ixRowS, ixRow, ouIxRowS, ouIxRow, rowNewTran; 
	//------------------------------------------

	var nfileW,ixRowW, rowW, tranW;
	//-----------
	var wList;
	var sw_someTranMissing = false;  // sometimes the automatic translator does some mistakes 
	var wT;
	//----------------------------
	for(var z=0; z < lenTran; z++) {
	
		wT = rowTranList[z]	
		
		//console.log("??anto showRows z=" + z + " ==>" + wT  + "<==")
		/**
		1;;2;;Erstes Kapitel
		3;;4;;Gustav Aschenbach oder von Aschenbach, wie seit seinem fuenfzigsten
		4;;5;;Geburtstag amtlich sein Name lautete, hatte an einem
		**/
		if (wT == "") {console.log("??anto 1  continue"); continue;}
				
		wList = wT.split(";;") ;
		if (wList.length != 3) { 
			wT = replaceSepar(wT);
			wList = wT.split(";;") ;
		}
		if (wList.length != 3) { 
			//console.log("??anto 2  continue; " ,  wList)
			continue;
		}
		[ouIxRowS, ixRowS, rowNewTran] = wList ;   			
		 
		try {
			ouIxRow = parseInt(ouIxRowS)    // row index  in the row html page   
			ixRow   = parseInt(ixRowS)      // row index  in the row DB    ( that is:  inputTextRowSlice[ixRow] in GO )
		} catch(e) { 
			console.log("??anto 3  continue")
			continue; 
		}	
		if (ouIxRow >= lenW) {
				console.log("showWordsButton() error2  entry z=" + z + " = " + wt  + " ixRow=" + ixRow , " >= lenW=" , lenW ); 
				continue;
		} 
		/***
		oT = rowToStudy_list[z];	
			//console.log("\t fun_showRowList(", wh,")",  "  2 for z=", z, " => " , oT); 
		if (oT == "") {  continue;}
		if (oT.substring(0,2) != ";;") { continue; }
		[nfileS,ixRowS, rowS, tranS] =  oT.substring(2).split(";;") ;  // eg. ;;0;2;; Primo capitolo	
		**/
		try {
			[nfileW,ixRowW, rowW, tranW] = rowToStudy_list[ouIxRow].substring(2).split(";;");
		} catch(e1) {
			console.log(e1); 
			console.log("wT=" , wT)
			console.log("wList=", wList)
			console.log("ouIxRow=" + ouIxRow )  
			continue;
		}
		
		if ( parseInt(ixRowW) != ixRow) {
			sw_someTranMissing= true;	
			console.log("showRowsButton() error4 entry z=" + z + " = " + wT  + "\n\t rowToStudy_list[ouIxRow="+ ouIxRow +"]=" +  rowToStudy_list[ouIxRow] +  
				"\n\tixRowW=" + ixRowW + " ixRow=" + ixRow);				
			continue; 
		} 
		newRowTran[ouIxRow] = 1; 
		
		//console.log("anto newTran[ixzNum=" + ixzNum + "] = 1" ); 
		
		rowToStudy_list[ouIxRow] = ";;" + nfileW +";;" + ixRow + ";;" + rowW + ";;" + rowNewTran  ; // update with translation 	
	
	}  // end of for(var z ...
	//--------------------------	
	
	if (sw_someTranMissing) {
		fun_showRowList("1")
		return;
	}		
	for (var i = 0; i < rowToStudy_list.length; i++) {
		//console.log("onlick_showRowsButton " ,  rowToStudy_list[i] );
		[nfileW,ixRowW, rowW, tranW] = rowToStudy_list[i].substring(2).split(";;");
		if (rowW == "") { continue; }
		if (tranW == "") { 
			sw_someTranMissing = true;  
			fun_showRowList("2")
			return;
		}
	}	
	write_row_dictionary(); 
	
	showRowsAndTranButton("3");
	
} // end of onclick_showRowsButton()

//---------------------------

function showRowsAndTranButton(wh) {	
	
	var showList = '' 
	
    var word1, ix1, nrow, wLemma1;
	var riga;
	
	var wordOrig2, wordTran2;
	
	
	var wordTran = ""
	var row0; 
	var nfile, ixRow, origRow, origTran; 
	
	string_tr_xx = "\n" + prototype_tr_m2_tts + "\n" + prototype_tr_m1_tts + "\n" + prototype_tr_tts; 
	word_tr_allclip =  "\n" + prototype_word_tr_m2_tts + "\n" + prototype_word_tr_m1_tts + "\n" + prototype_word_tr_tts; 
		
	//--------------	
	var txt1p, text_tts, tranRow; 
	var nFileR, nfile_zero;
	var first= -1, last=-1;
    for (var i = 0; i < rowToStudy_list.length; i++) {
		/*
		row		
		;;0;;2;; Erstes Kapitel;; Primo capitolo
		;;0;;3;; ;; 
		;;0;;4;; Gustav Aschenbach oder von Aschenbach, wie seit seinem fuenfzigsten;; Gustav Aschenbach o von Aschenbach, come ha fatto sin dai suoi cinquant'anni
		;;0;;5;; Geburtstag amtlich sein Name lautete, hatte an einem;; compleanno, era il suo nome ufficiale, era l'uno		
		*/
		row0 = rowToStudy_list[i]
		if (row0=="") continue;
		//console.log("row " , row0 )
		if (row0.substring(0,2) != ";;") continue;
		[nfile, ixRow, origRow, tranRow] = row0.substring(2).split(";;");   
	
		txt1p = evidenzia(word_to_underline, origRow); 
		text_tts = "";
		
		nFileR = nfile + "_" + ixRow ; 
        let riga = string_tr_xx.replaceAll("§1§", i).
			replaceAll("§4txt§", origRow).replaceAll("§5txt§", tranRow).
			replaceAll("§4ptxt§", txt1p).
			replaceAll("§ttstxt§", text_tts).
			replaceAll("§6§", nFileR).
			replaceAll("§nfile§",nfile)	;
		if (first < 0) first = i;
		last = i; 	
					
		showList    += riga + "\n";	
		
    }
	//---------------------------------------------------
	eleTabSub_tbody.innerHTML = showList;
	
	if ( (last - first) > 0) {
		let eleF = document.getElementById("b1_" + first);
		let eleT = document.getElementById("b2_" + last);
		onclick_tts_arrowFromIx(eleF, first, 5);
		onclick_tts_arrowToIx(  eleT, last    );		
	}
		
	onclick_jumpFromToPage( page1,0, page2);  
	

} // end of showRowsAndTranButton

//-------------------------------------------------

function write_row_dictionary() {
	var nfileW,ixRowW, rowW, tranW; 
	var word1, ix1, nrow, wLemma1, wordTran, col1;
	
	var newTranRow=0;
	var listNewTranRows = "";
	
	//console.log("\n----------------------\nwrite_row_dictionary() rowToStudy_list=" ,  rowToStudy_list ,"\n----------")
	
	for (var i = 0; i < rowToStudy_list.length; i++) {
		if ( rowToStudy_list[i] == "") continue; 
		//console.log("write " ,  rowToStudy_list[i] )
		
		col1 = rowToStudy_list[i].substring(2).split(";;");		
		//[nfile, ixRow, origRow, tranRow] = row0.substring(2).split(";;");   
		//console.log("\tcol1=", col1)
		nfileW=col1[0]; 
		ixRowW=col1[1];  
		rowW  =col1[2]; 
		tranW =col1[3]; 
		if ((ixRowW == "1374") || ( ixRowW == "1773") ) { console.log("write_row_dictionary() ",  rowToStudy_list[i], " tranW=", tranW) }
		
		
				if (tranW == "") { continue; }
		
		//console.log("\t" , [nfileW,ixRowW, tranW] )
		if (newRowTran[i]==1) {                                                                 
			newTranRow++;                                     
			listNewTranRows  += "\n" + ixRowW + ";" + tranW ;   // new line for dictionary 
		}
	}
	//------------
	
	//console.log("go_write_row_dictionary(" + listNewTranRows )
	
	go_write_row_dictionary(  listNewTranRows );  		
	
} // end of write_row_dictionary

//------------------------------------------