"use strict";
/*  
ClipByClip: A tool to practice language comprehension
Antonio Cigna 2021/2022
license MIT: you can share and modify the software, but you must include the license file 
*/ 
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */	 
//---------------------------------------------------------


var word_separator = ".,.;:?!_+-\[\]\(\)"  + "\t\n\r" ;  // word separator characters 

//----------------------------------------------------
// This function returns an XML string with all the messages from the application.
// xml doesn&apos;t accept &apos;<&apos; and &apos;&&apos; characters,
// but here you can use the following html markup: <br><b></b> <ul><li></li></ul>
// and the following characters: & &apos; "
//-----
// If you want to edit a message you need to edit this file only (the texts in the html file are just for reminder).
// You can add any language using the English part as a base, as long as you change the first 2 lines and the last one appropriately:
//    <lang_xx> </lang_xx> where xx is the language identifier.
//    <id_language>xx</id_language>
//    <lang_name>Name of the language</lang_name> This line is never used in any script it is only used as a comment.
// The language used by the script is determined by the local language of the computer.
// The script gets the local language identifier, looks for the corresponding part in this file, if it can&apos;t find it, use the English one.
// for example: the identifier is fr, since the French part is missing (lang_fr) the English one (lang_en) is used.
//----
// The message id has the form <Vm...></Vm...>  
// where the first character can be one of A, B, C
//    A  message for  cbc_builder.html file    
//    B  message for  cbc_player.html file    
//    C  message for  cbc_Player_Words_ClipByClip.html file    
//    H  message for  ...  DOC/DOC_english/doc_en.html     
//    S  message for  ...  SRT_v2_from_TEXT.html

// The m... following A,B,C is the id  of the html element that will receive the message text (eg. id="m123")   
//
//----------------------------------------------------------------------------------------------------------------------------------------
// Questa funzione restituisce una stringa XML con tutti i messaggi dell&apos;applicazione. 
// xml non accetta i caratteri &apos;<&apos; e &apos;&&apos;,
// ma qui puoi usare i seguenti marcatori html: <br><b></b> <ul><li></li></ul>
// e i seguenti caratteri: & &apos; "
//-----
// Se vuoi modificare un messaggio devi modificare soltanto questo file (quelli nel file html servono soltanto come promemoria)
// Puoi aggiungere qualsiasi lingua usando come base la parte inglese, a patto di modificare opportunamente le prime 3 righe e l&apos;ultima:
//    <lang_xx>   </lang_xx>   dove xx è l&apos;identificatore della lingua.
//    <id_language>xx</id_language>
//    <languageName>Nome della lingua usata</languageName>  Questa riga non  è mai usata in nessuno script serve soltanto come commento.
// La lingua utilizzata dallo script è determinata dalla lingua locale del computer.
// Lo script ottiene l&apos;identificativo xx della lingua locale, cerca la parte corrispondente in questo file, 
// se non la trova, utilizza quella in inglese.
// per esempio: l&apos;identificativo è fr, poiché manca la parte francese (lang_fr) viene utilizzata quella inglese (lang_en).
//----
// L&apos;id del messaggio ha la forma <Vm...></Vm...>
// dove il primo carattere può essere A, B, o C
// 		A messaggio per il file cbc_builder.html
//      B messaggio per il file cbc_player.html
//      C messaggio per il file cbc_Player_Words_ClipByClip.html
// La m... che segue A,B,C è l&apos;id dell&apos;elemento html che riceverà il testo del messaggio  (es. id="m123")
//               
//---------------------------------------------------------------------------------------------------------------------------------------

function get_messages() {

	var xml_text = `
<messages>
	<lang_en>		
		<id_language>en</id_language>	
		<languageName>English</languageName>		
		<Vm001>Select a voice</Vm001>	
		<Vm002>language</Vm002>
		<Vm003>voice</Vm003>			
		<Vm004>continue</Vm004>		
		<Vm005>select start</Vm005>
		<Vm006>select end</Vm006>
		<Vm007>show / hide<br>text</Vm007>
		<Vm008>show / hide<br>translation</Vm008>			
		<Vm013>word<br>by<br>word</Vm013>	
		<Vm014>A tool to <br>improve foreign language §oralcomprehension§</Vm014>	
		<Vm015>by listening to a text <br>read one line at time, one word at time
			<br><br>at each click the row or word is read by the indicated voice
			<br>even at reduced speed if required
		</Vm015>	
		<Vm016>Paste the <b>§1§</b> text here below</Vm016>		
		<Vm017>Paste the line by line translation here below </Vm017>
		<Vm018>(if it doesn't exist write 3 dots ...)</Vm018>						
		<Vm100><b>To synchronize subtitles with speech</b></Vm100>
		<Vm101><ul><li>Select a group of subtitle lines </li></ul></Vm101>
		<Vm102>Practice<br>by listening and reading<br>only a few subtitle lines at time</Vm102>
		<Vm103>Practice<br>by listening<br>only a few seconds at a time</Vm103>
		<Vm104>Practice<br>by listening (synthetic voice) and reading </Vm104>
		<Vm105>Rate</Vm105> 
		<Vm106>end time</Vm106>
		<Vm107>seconds</Vm107>
		<Vm108>since the <br>second</Vm108>
		<Vm109>per <br>second</Vm109>
		<Vm110>text</Vm110>
		<Vm111>Subtitles</Vm111>			
		<Vm112>Press the button of the line that ends with the last word spoken</Vm112>
		<Vm113>subtitle lines</Vm113>
		<Vm114>subtitle line</Vm114>
		<Vm115>show all subtitles</Vm115>							
		<Vm116>hide all subtitles</Vm116>
		<Vm117>increased by</Vm117>
		<Vm118>decreased by</Vm118>
		<Vm119>Bilingual Text</Vm119>	
		<Vm120>spoken in</Vm120>	
		<Vm121>text</Vm121>
		<Vm122>Play the chosen voice</Vm122>                          
        <Vm123>Play a voice in turn</Vm123>    
		<Vm124>Play pause between words</Vm124>
        <Vm125>N.</Vm125>	
		<Vm126>Pitch</Vm126>
		<Vm127>Speed</Vm127>
		<Vm128>Pause</Vm128>
		<Vm129>Resume</Vm129>
		<Vm130>Cancel</Vm130>		
		<Vm131>Go Back</Vm131>  		
		<Vm132>the text in source language is missing</Vm132>	
		<Vm133>the translated text is missing</Vm133>	
		<Vm134>but if that's ok, write 3 dots in a row <b>§...§</b></Vm134>  	
		<Vm135>Select the first voice to read the text</Vm135>
		<Vm136>the other voices in the same language will read in turn</Vm136>
		<Vm137>continue</Vm137>
		<Vm138>§1§ text</Vm138>
		<Vm139>specify the maximum line length</Vm139>
		<Vm140>continue</Vm140>
		<Vm141>oral comprehension</Vm141>	
	</lang_en>	
	<lang_it>
		<id_language>it</id_language>	
		<languageName>Italiano</languageName>	
		<Vm001>Seleziona una voce</Vm001>
		<Vm002>lingua</Vm002>
		<Vm003>voce</Vm003>
		<Vm004>continua</Vm004>
		<Vm005>seleziona inizio</Vm005>
		<Vm006>seleziona fine</Vm006>
		<Vm007>mostra / nascondi<br>testo</Vm007>
		<Vm008>mostra / nascondi<br>traduzione</Vm008>		
		<Vm013>parola<br>per<br>parola</Vm013>
		<Vm014>Uno strumento per migliorare la<br>§oralcomprehension§<br> delle lingue straniere</Vm014>
		<Vm015>ascoltando un testo <br>letto una riga per volta, una parola per volta
			<br><br>ad ogni click la riga o la parola viene letta dalla voce indicata 
			<br>anche a velocità ridotta se richiesto   
		</Vm015>
		<Vm016>Incolla qui sotto il testo in <b>§1§</b></Vm016>
		<Vm017>Incolla la traduzione riga per riga qui sotto </Vm017>
		<Vm018>(se non esiste scrivere 3 punti...)</Vm018>
		<Vm100><b>Per sincronizzare i sottotitoli con il parlato</b></Vm100>
		<Vm101><ul><li>Seleziona un gruppo di righe di sottotitoli </li></ul></Vm101>
		<Vm102>Esercitati<br>ascoltando e leggendo<br>solo poche righe di sottotitoli alla volta</Vm102>
		<Vm103>Esercitati<br>ascoltando<br>solo pochi secondi alla volta</Vm103>
		<Vm104>Esercitati<br>con l'ascolto (voce sintetica) e la lettura </Vm104>
		<Vm105>Tasso</Vm105>
		<Vm106>ora di fine</Vm106>
		<Vm107>secondi</Vm107>
		<Vm108>dal <br>secondo</Vm108>
		<Vm109>al <br>secondo</Vm109>
		<Vm110>testo</Vm110>
		<Vm111>Sottotitoli</Vm111>
		<Vm112>Premere il pulsante della riga che termina con l'ultima parola pronunciata</Vm112>
		<Vm113>linee di sottotitoli</Vm113>
		<Vm114>riga dei sottotitoli</Vm114>
		<Vm115>mostra tutti i sottotitoli</Vm115>
		<Vm116>nascondi tutti i sottotitoli</Vm116>
		<Vm117>aumentato di</Vm117>
		<Vm118>diminuito di</Vm118>
		<Vm119>Testo bilingue</Vm119>
		<Vm120>parlato in</Vm120>	
		<Vm121>testo</Vm121>	
		<Vm122>Play la voce scelta</Vm122>                          
        <Vm123>Play una voce a turno</Vm123>    
		<Vm124>Play pausa tra le parole</Vm124>
        <Vm125>N.</Vm125>	
		<Vm126>Tono</Vm126>
		<Vm127>Velocità</Vm127>
		<Vm128>Pausa</Vm128>
		<Vm129>Riprendi</Vm129>
		<Vm130>Annulla</Vm130>
		<Vm131>Indietro</Vm131>  
		<Vm132>manca il testo in lingua originale</Vm132>	
		<Vm133>manca la traduzione</Vm133>	
		<Vm134>ma se va bene così, scrivi al suo posto 3 puntini di seguito <b>§...§</b></Vm134>  	
		<Vm135>Seleziona la prima voce che dovrà leggere il testo</Vm135>
		<Vm136>le altre voci nella stessa lingua leggeranno a turno</Vm136>
		<Vm137>continua</Vm137>
		<Vm138>testo §1§</Vm138>
		<Vm139>specifica la lunghezza massima delle righe</Vm139>  
		<Vm140>continua</Vm140>	
		<Vm141>comprensione orale</Vm141>	
	</lang_it>
</messages>	
`; // end of xml_text ( ` alt + 96 )

return xml_text;

} // end of get_messages()
//=======================================================================
