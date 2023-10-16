"use strict";
/*  
ClipByClip: A tool to practice language comprehension
Antonio Cigna 2021/2022
license MIT: you can share and modify the software, but you must include the license file 
*/ 
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */	 

//==============================
/***
This file load the messages contained in the container (cbc_MESSAGE.msg file ) into corresponding html elements.

All messages are written in a string in xml format in a js file (the message container)
they are grouped for language id 
	<messages>
		<lang_en>
			<lang_name>English</lang_name>								
			<Bm001>ERROR</Bm001>									
			<Bm002>This html file has no parameters to use.</Bm002>	
		</lang_en>	
		<lang_it>
			<lang_name>Italiano</lang_name>
			<Bm001>ERRORE</Bm001>
			<Bm002>Questo file html non ha parametri da usare.</Bm002>
			...
		</lang_it>		
	</messages>

The two character language id (eg. en (English, it (italian) )  is got from the local language. 
if the group for the local language is missing the 'lang_en' (English) is used.    

The key for each message line is prefixed by a 1byte character which identify the script which uses it and by the 'm' letter.  
The key without the first byte is egual to the id of the corresponding html element. 

As exception to the xml rules a message can contain  <b></b> and <br> markers.      

The application using these file scripts must contain 
	a function called 'custom_message_change()' which can be empty and which can be used to modify the messages

This script file is executed onload by the html file: eg.
	   <script src="./cbc_player/MESSAGE_manager.jstxt"  onload="messageMain( "B" );"></script> 	

**/

//==============================
var parser, xmlDoc;
var DEFAULT_language_test =  "_antonio_test_"; 
var myLocalLanguage = "";  
//---------------------------------------

function execParser() {
	var xml_text = get_messages();  // function defined in 'cbc_message.msg' file 
	
	//<?xml version="1.0" encoding="UTF-8"?>
	var z1= xml_text.indexOf('?>'); 
	if (z1>0) { xml_text = xml_text.substr(z1+2); }
	
	xml_text = xml_text.replace(/\&/g      , "&amp;"      ).
	
						replace(/\<br\>/g  , "&lt;br&gt;" ).
						
						replace(/\<b\>/g   , "&lt;b&gt;"  ).
						replace(/\<\/b\>/g , "&lt;\/b&gt;").	

						replace(/\<ul\>/g   , "&lt;ul&gt;"  ).
						replace(/\<\/ul\>/g , "&lt;\/ul&gt;").		
						
						replace(/\<li\>/g   , "&lt;li&gt;"  ).
						replace(/\<\/li\>/g , "&lt;\/li&gt;").								
				
						replace(/\'/g      , "&apos;"     ).
						replace(/\"/g      , "&quot;"     );
	
	//console_log_1( xml_text);
	
	parser = new DOMParser();
	
	xmlDoc = parser.parseFromString(xml_text,"text/xml");

} // end of execParser()

//------------------------------------------------
function console_log_1( str1 ) {
	
	//console.log(str1) 
}
//-------------------------------------------------
function update_HtmlEle_MsgById(parm_pgm_ABCH, id_language) {
	if (xmlDoc == null) return; 
	
	var sw_debug = true; //false;
	
	var defaut_id_language = "en";
	
	if ( window.location.pathname.toLowerCase().indexOf( DEFAULT_language_test ) >= 0) {
		id_language = "xx";   
	}
	if (testDefault) id_language = "xx";  
	console_log_1("id_language=" + id_language); 

	myLocalLanguage = id_language; 
	
	var langKey = 'lang_' + id_language; 
	
	let list_msg_id_val; 
	let num_msg = 0;  
	var numOK=0;
	var numKO=0; 
	var str1=""; 
	

	for (var n=0; n < 3; n++) {
		try {
			list_msg_id_val = Array.from( xmlDoc.getElementsByTagName( langKey )[0].children ).map(
									({nodeName:msgId, textContent:msgText}) => ({msgId, msgText})
								);						
								
			num_msg = list_msg_id_val.length; 					
			break;	
		} catch(e1) {
			str1 += "language '" + id_language + "' not found,  used default '" + defaut_id_language + "'"; 
			num_msg = 0; 
			langKey = 'lang_' + defaut_id_language; 
		} 		
	}	
					
	str1 +="\n\tmessages got from: '<" + langKey + ">'\n" ;
	console_log_1(str1 + "  num_msg=" + num_msg);
	
	var txt2;
	for(var z1=0; z1 < list_msg_id_val.length; z1++) {
		var eleM = list_msg_id_val[z1];
		var msgId0 = eleM.msgId;
		if (msgId0 == "lang_name") {
			console_log_1("load messages for " + eleM.msgText);  
			continue; 
		}	
		//console_log_1("message " + eleM.msgId	 +   " parm_pgm_ABCH=" + parm_pgm_ABCH + "<=="); 	
		if (eleM.msgId.substr(0,1) != parm_pgm_ABCH) { continue; } 
		var msgIdH = msgId0.substring(1); 
		var eleH = document.getElementById( msgIdH );
		if ( eleH ) {			
			//if (sw_debug) console_log_1( eleM.msgId + " "  + eleM.msgText); 
			txt2 =  custom_message_change( eleM.msgText );  // this function must exist in an application script file 		
			eleH.innerHTML = txt2; 		
			numOK++;	
		}
		else {
			if (sw_debug) {
				console_log_1("no html id found matching " + eleM.msgId + " " + eleM.msgText); 
				numKO++; 
			}	
		}		
	}
	console_log_1(numOK + " text messages replaced corresponding html elements"); 
	if (numKO > 0) {
		console_log_1(numKO + " message didn't match any html elements"); 
	}	
	
} // end of update_HtmlEle_MsgById(  

//----------------------------------------------------------------------------------

function messageMain( parm_pgm_ABCH, parm_lang00) {
	if (parm_lang00) {
		console_log_1("messageMain(" + parm_pgm_ABCH +", " + parm_lang00 + ")");
	} else {		
		console_log_1("messageMain(" + parm_pgm_ABCH + ")");
	}
	execParser(); 
		
	let myLang = "en"; 
	let local_language = navigator.language;
	if (local_language) {
		myLang = local_language; // .substr(0,2);
		console_log_1("local language '" + myLang + "'"); 
	}
	
	if (parm_lang00) {
		if (parm_lang00 != "") {
			myLang = parm_lang00; 
			console_log_1("parameter language '" + myLang + "' replaces local language"); 
		}
	} 
	
	var parm_lang = ( myLang.split("-")[0] ).trim().toLowerCase()  ; 
	
	
	//console_log_1(Array.from( xmlDoc.getElementsByTagName( 'lang_en')[0].children ) ); 
	
	update_HtmlEle_MsgById(parm_pgm_ABCH, parm_lang); 
	
}
//------------------------------------
function get_languageName( en_GB ) {
	
	var la =  (en_GB+"--").replaceAll("_","-").split("-");	
	var id_lang    = la[0];
	var id_country = la[1]; 
	
	if (myLocalLanguage == "xx") {
		myLocalLanguage = "en";
	}
	id_lang    = (""+id_lang).trim().toLowerCase();
	id_country = (""+id_country).trim().toUpperCase();
	const countryExt  = new Intl.DisplayNames([ myLocalLanguage ], { type: 'region'   } );
	const languageExt = new Intl.DisplayNames([ myLocalLanguage ], { type: 'language' } ); 
	var r_lang = ""; var r_country=""; 
	
	if (id_lang != "")    r_lang    = languageExt.of( id_lang    ); 
	if (id_country != "") r_country = countryExt.of(  id_country );  
	
	r_lang    = r_lang.substr(0,1).toUpperCase()    + r_lang.substr(1); 
	r_country = r_country.substr(0,1).toUpperCase() + r_country.substr(1); 
	
	return r_lang + " - " + r_country;  
	
}
//-----------------------------------------		