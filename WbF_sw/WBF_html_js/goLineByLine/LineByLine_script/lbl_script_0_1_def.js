"use strict";
/*  
LineByLine: A tool to practice language comprehension
Antonio Cigna 2023
license MIT: you can share and modify the software, but you must include the license file 
*/
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */
//----------------------------------------------

let word_to_underline = "1234"; 

var currScript = document.currentScript.src; var bar1 = currScript.lastIndexOf("\\");var bar2 = currScript.lastIndexOf("/"); 
//console.log("LOADED file SCRIPT " + currScript.substring( 1+Math.max(bar1,bar2) )) ;	
//----------------------------------------------------------------------------------------
let swdebug = false;
let sw_word_script=false; 
let word_last_BoldRow;

let ele_voxDisplay = document.getElementById("id_voxDisplay"); 
let ele_voxLangDisplay = document.getElementById("id_voxLangDisplay");

const NO_VIDEO_AUDIO_FILE = "noVIDEO_noAUDIO".toLowerCase();
let sw_is_no_videoaudio = false;

let clock_timer_symb = "&#x23f1;";
let playLoop_symb = "&infin;";
let speakinghead_symb = "&#128483;";
let magnifyingGlass_symb = "&#128270;";
let pause_symb = "&#x23F8;";
let play_symb = "&#x23F5;";
let word_pause_symb = "&#x1d110;"; 

let openbook_symb = "&#128214;";
let closedbook_symb = "&#128213;";
let left_arrow_symb = "&#8592;";
let right_arrow_symb = "&#8594;";
let breakwords_symb = "/|/";

let Clip_startTime = 0;
let Clip_stopTime = 0;
let clipFromRow = 0;
let clipFromRow_min = 0;
let clipToRow = 0;
let clip_play_time_interrupt = 0;

let sw_the_are_no_subtitles = false;
const NO_TEXT_NO_SUBTITLES = "NO_TEXT_NO_SUBTITLES";

let sw_CLIP_play = false;

let CLIP_Loop_StartTime = 0;
let CLIP_Loop_StopTime = 0;

let sw_CLIP_row_play = false;



let sw_active_show_lastSpokenLineTranslation = false;

let CLIP_Row_StartTime = 0;
let CLIP_Row_StopTime = 0;
let CLIP_Row_StopIx = -1;

let last_ixClip = -1;

let ele_last_tran_line;

//let ele_tts = document.getElementById("id_tts"); // synthetic voce  <div >...</div>
let sw_tts = false;
let sw_tts2;

//
let ONEDAY = 24 * 60 * 60 * 1000;
let start_milliseconds = Date.now();

let num_day_today = Math.floor(start_milliseconds / ONEDAY);

let sw_audio = false;


let title1 = "";

//--------------------------------------------------
let INITIAL_hex_BG_color = "#C8BEBC"; //  "#FFFFF";
let INITIAL_hex_FG_color = "#000000";
let sw_show_time_in_subtitle = false;
let sw_show_clip_num = true;
let numOrig = 0;
let numTran = 0;


//-------------------------------------------------------
let vid_duration = 0;

let ele_video_speed;
let video_native_height;
let video_native_width;
let newVidH, newVidW;
let newVidHperc, newVidWperc;
let inp_text_orig;
let inp_text_tran;

let ele_mask_dragsub = document.getElementById("id_mask_dragsub");
let eleTabSub = document.getElementById("id_tabSub");
let eleTabSub_tbody = document.getElementById("id_tabSub_tbody");

let selected_voice_ix                    = 0 ;     // eg. 65 	 
let selected_voiceName                   = "";     // eg. Microsoft David - English (United States)"; 	
let	selected_voiceLangRegion             = "";     // eg. en-us	
let	selected_voiceLang2                  = "";     // eg. en

let isVoiceSelected = false;  

let selected_numVoices = 0;
let maxNumVoices = 9999; // 9

let last_pitch = 1;
let last_rate  = 1;
let last_volume = 1;

let ele_playNextVa_from_hhmmss_value;
let ele_replayVa_from_hhmmss_value;
let ele_replayVa_to_hhmmss_value;

let radio_type1_SECONDS = "a";
let radio_type2_SECS_END_DIALOG = "b";
let radio_type4_LINES = "d";

let CLIP_dur_line_TYPES = radio_type4_LINES;

let LS_voice_index = -1;



//----------------------------------------------------------------

let cbc_LOCALSTOR_key = "";

//  the LS_... variables here after have their values stored in window.localStorage so that they can be retrieved in the next sessions 
//  all this value are put in a list and saved in one variable the name of which contains the title of the page (each page has its own values)  

let LS_clip_secs0b_value = 3;
let LS_clip_secs1d_value = "3-false-true";
let LS_clip_secs2c_value = 3;
let LS_clip_lines_value = 3;

let LS_clip_checked_sw_type = radio_type2_SECS_END_DIALOG; // intial default
let LS_clip_checked_type_value = 3;


let LS_stor_ext_time = 1.5;
let LS_stor_playnext_replay = "00:00:00,000;;00:00:00,000;;00:00:00,000;;";
let LS_subDeltaTime = 0;
let LS_colorBG = "#f3c89d";
let LS_colorTx = "black";
let LS_sub_beg_delta = 0;
let LS_sub_end_delta = 0;
let LS_sub_force_visible = true;


let sw_end_dialog_sentence = true;
let sw_end_dialog_overlap = true;


let cbc_LOCALSTOR_ctrkey = "";
let LS_CTR_1run_num = 0; // number of runs of this video since  building   
let LS_CTR_2run_days = 0; // number of days of runs  
let LS_CTR_3run_num_play = 0;
let LS_CTR_4run_elapsed = 0; // total elapsed time of the runs  
let LS_CTR_5run_videoRunTime = 0; // total of playback elapsed time 
let LS_CTR_6logon_num_play = 0; // number of play enter since logon   
let LS_CTR_7logon_elapsed = 0; // total elapsed time of the runs  
let LS_CTR_8logon_videoRunTime = 0; // total of playback elapsed time 
let LS_CTR_9numday_today = 0; // num.day  starting 1970 
let LS_CTR_10run_num_lines = 0; // num.of subtitle lines 
let LS_CTR_11run_num_words = 0; // num.of subtitle words 
let LS_CTR_12logon_num_lines = 0; // num.of subtitle lines 
let LS_CTR_13logon_num_words = 0; // num.of subtitle words 

//-------------------------------------------------------------
let ele_last_play;
let LAST_time_change_ix = 1;
let LAST_time_change_secs = 0;
let PLAYCLIP_TYPE = 0;
let PLAYCLIP_FROM_TIME = 0;
let PLAYCLIP_TO_TIME = 0;
let PLAYCLIP_FROM_LINE = 0;
let PLAYCLIP_TO_LINE = 0;
let CLIP_ENDTIME_PLUS = 0;
let CLIP_ENDTIME_MINUS = 0;
let SW_CLIP_ENDED = false;
//--------------------------------------------------------

let playTRIGGER_clip = 1;
let playTRIGGER_row = 2;
let playTRIGGER_emul = 3;

let lastPlayTrigger = playTRIGGER_emul;
let lastPlayRowFromIx, lastPlayRowToIx, lastPlayRowFromTime, lastPlayRowToTime, lastPlayRowLoop;
let lastPlayListFrom = [];
let lastPlayListIx = -1;
let last_BoldRow;
//----------------------------------------
let TO_TIME_TOLERANCE = 0.5;


let ele_replay_from_secs_innerHTML;

let ele_replayVa_from_row_value;

let ele_replay2_from_row_innerHTML;

let ele_replay_to_secs_innerHTML;

let ele_replayVa_to_row_value;

let ele_replay2_to_row_innerHTML;



let ele_clip_subtext;
let html_parms_queryString = "";
//------------------------



let ele_dragSubT;
let ele_dragSubT_anchor;

let wScreen;
let hScreen;
let subtitles_beg_delta_time;

let src1;
let vid;
let MAX999;
let path1;
let sayNODIALOG = "-NODIA-";
let f1;
let f2;
let f3;
let barra;


let lastClipTimeBegin;
let lastClipTimeEnd;
let ele_time_video;
let ele_sub_filler;
let ele_subOrigText2;
let ele_subTranText2;
let ele_showOrigText2_open;
let ele_showOrigText2_close;
let ele_showTranText2_open;
let ele_showTranText2_close;
let ele_subOrigSilent;
let ele_subOrigSilentH;
let ele_main_subt = document.getElementById("id_main_subt");

let list_elemSub = ["", ""];
let list_elemSub_display = [false, false];

let line_list_o_number_of_elements = 0;
let line_list_t_number_of_elements = 0;

let sw_sub_onfile = false;
let sw_sub_orig = false;
let sw_sub_tran = false;
let sw_no_subtitle = false; // no subtitles ( neither inside the video, neither in any file apart

let LIMIT_MIN_TIME_CLIP;
let MIN_ixClip = 0;
let MAX_ixClip = MAX999;

let inp_row_orig = [];
let inp_row_tran = [];

let number_of_subtitle_endsentence = 0;
let number_of_subtitle_time_overlap = 0;

let line_list_o_from00 = [];
let line_list_o_to00 = [];
let line_list_o_maxto00 = [];

let line_list_o_from1 = [];
let line_list_o_to1 = [];
let line_list_o_maxto1 = [];
let line_list_orig_text = [];
let line_list_orig_nFileR = []; 
let line_list_orig_tts = [];
let line_list_o_tran_ixmin = [];
let line_list_o_tran_ixmax = [];

let line_list_t_from00 = [];
let line_list_t_to00 = [];
let line_list_t_maxto00 = [];

let line_list_t_from1 = [];
let line_list_t_to1 = [];
let line_list_t_maxto1 = [];
let line_list_tran_text = [];

//orig_and_tran_in_one_line();
let LAST_SEARCH_o_time = -1;
let LAST_SEARCH_o_ix;
let LAST_SEARCH_o_fromto;

let LAST_SEARCH_t_time = -1;
let LAST_SEARCH_t_ix;
let LAST_SEARCH_t_fromto;
//------------------------------------



let ele_ctl_playpause = document.getElementById("id_ctl_playpause");
ele_ctl_playpause.children[0].innerHTML = ele_ctl_playpause.children[0].innerHTML.replace("§play_symb§", play_symb);
ele_ctl_playpause.children[1].innerHTML = ele_ctl_playpause.children[1].innerHTML.replace("§pause_symb§", pause_symb);
let ele_ctl_slider = document.getElementById("id_ctl_slider");
let ele_ctl_value = document.getElementById("id_ctl_value");
let ctl_slider_maxValue_hhmm = 0;
let myLang = navigator.language; // eg.  it-IT
let decimal_point = (0.123).toLocaleString(myLang).toString().substr(1, 1);


//-----------------------------

let word_fromIxToIxLimit = [-1, -1];
let word_fromIxToIxButtonElement = [null, null];


//----------------------------------------------

let clip_reset_BG_color = "white";
let clip_somerow_BG_color = "lightgrey";


let begix, endix;
let fromIxToIxLimit = [-1, -1];
let fromIxToIxButtonElement = [null, null];

let save_last_oneOnlyRow = "";
let save_last_oneOnly_idtr = "";
save_last_oneOnlyRow = "";
save_last_oneOnly_idtr = "";

let hide_translation_symb = '<span style="font-weight:bold;min-width:4em;">t?</span></span>';
let show_translation_symb = '<span style="font-weight:bold;">T</span></span>';


let note_arrow1 = '<span style="font-size:2em;width:auto;height:1.4em;">' + right_arrow_symb + '</span>';
let note_arrow2 = '<span style="font-size:2em;width:auto;height:1.4em;">' + left_arrow_symb + '</span>';
let note_speaking = '<span style="font-size:2em;width:auto;height:1.4em;">' + speakinghead_symb + '</span>';

let note_magnifyingGlass_symb = '<span style="font-size:2em;width:auto;height:1.4em;">' + magnifyingGlass_symb + '</span>';

let note_loop_speaking = '<span style="font-size:2em;width:auto;height:1.4em;">' + playLoop_symb + '</span>';
let note_hide_sub = '<span style="font-size:2em;width:auto;height:1.4em;">' + openbook_symb + '</span>';
let note_show_sub = '<span style="font-size:2em;width:auto;height:1.4em;">' + closedbook_symb + '</span>';
let note_show_tran = '<span style="font-size:2em;width:auto;height:1.4em;">' + show_translation_symb + '</span>';
let note_hide_tran = '<span style="font-size:2em;width:auto;height:1.4em;">' + hide_translation_symb + '</span>';
let note_breakwords = '<span style="font-size:2em;width:auto;height:1.4em;">' + breakwords_symb + '</span>';
let note_clock_timer_symb = '<span style="font-size:2em;width:auto;height:1.4em;">' + clock_timer_symb + '</span>';


//--------------------------------

//js2___________________  js2


let last_ele_analWords_id; 
let last_ele_analWords_tr;
let last_ele_analWords_height;
//js3___________________  	

//js4___________________  	

let startTime;
let txt_length; 
let sw_pause = false; 
let sw_cancel = false;
let time_limit = 15; // in seconds  //  it seems that  an utterance can't last more     
let ELAPSED_TIME_SPEECH_LIMIT = 1000 * ( time_limit - 1) ;  

let tot_norm_time = 0;
let tot_txt_len =0;	
let tot_norm_mill_char = 0; 	  
let tot_norm_str_leng_limit = 0;	 
let TXT_SPEECH_LENGTH_LIMIT = 80; // initial value is updated according to the actual duration runs
//----
let TTS_LOOP_begix=-1;
var	TTS_LOOP_endix=-1; 
var	TTS_LOOP_swLoop=false; 	
let TTS_LOOP_elem;   
//--------------------------
let voice_toUpdate_speech;
let speech_volume = 1;
let speech_rate = 1;
let speech_pitch = 1;
let utteranceList = [];
//-----------------
let textLines = [];

//---------------------

//------------
let lastRow = -1;
let lastCol = -1;
let lastBoldCell;
let last_blue_cell;


//let ele_tab =document.getElementById("tab1"); 
/**
let myVoice;
let voices  = [];   // all voices from synth.. getVoices() 
**/
let listVox = [];   // selected voices only   
let voiceList2=[]; 
let totNumMyLangVoices=0; 
let lastNumVoice = 0; 
let lastWordNumVoice=0;
//---------------------

let eleTabSub_diff_clientW, eleTabSub_diff_clientH; 

let eleTabSub_save_clientWidth, eleTabSub_save_clientHeight;  
let sw_eleTabSub_widthInit = true; 
let t_swMove = true;
let language_parameters=["","",""]; // from Builder parameters
//---------------------------

//let speech = new SpeechSynthesisUtterance();
let synth  = window.speechSynthesis;

//------

let x1_line = 0;
//===================================

var clip_legend = `<hr>
				
				<button class="buttonTD2" 
					onclick="
						{
							let ele_legend = document.getElementById('id_legend');
							if (ele_legend.style.display=='block' ) {
								ele_legend.style.display='none' ;
							} else {
								ele_legend.style.display='block' ;
							}
						}"  
						style="font-size:0.5em;"
					>
					<span style="font-size:1.0em;font-weight:bold;">Significato dei pulsanti</span>  			
					  
					<span style="font-size:0.8em;">
						${note_arrow1       }   ${note_arrow2       }   
						${note_speaking     }   ${note_loop_speaking}   
						${note_hide_sub   }   ${note_show_sub   }    ${note_hide_tran  }    ${note_show_tran  }
						<input type="range" min="0.25" max="2" value="1" step="0.25" style="width:3em;"> 
					</span>
					  
				</button>	
				<!--				
					${note_hide_tran  }   ${note_breakwords }    ${note_clock_timer_symb}
				-->
				
				<div id="id_legend" style="display:none; width:100%;border:0px solid black;text-align:center; font-size:0.8em; background-color:lightgrey;">
					<br>
					<div style="width:80%;border:0px solid black;display:flex;">
						<table style='font-size:0.5em;width:33%;color:black;border:0px solid black;text-align:left;'>	
							<tr><td style="width:5%;"></td></tr>	\n
							<tr><td>${note_arrow1       }</td><td>premi per stabilire l'inizio delle selezione delle righe</td></tr> \n 
							<tr><td>${note_arrow2       }</td><td>premi per stabilire la fine della selezione delle righe </td></tr> \n 
							<tr><td>${note_speaking     }</td><td>premi per riprodurre                                    </td></tr> \n							
							<tr><td>${note_loop_speaking}</td><td>premi per riprodurre e poi ripetere all'infinito  </td></tr> \n  	
						</table>
						<table style='font-size:0.5em;width:33%;color:black;border:0px solid black;text-align:left;'>		
							<tr><td style="width:5%;"></td></tr> \n
							<tr><td>${note_hide_sub   }</td><td>la riga è visibile, premi per nasconderla             </td></tr> \n 
							<tr><td>${note_show_sub   }</td><td>la riga è invisibile, premi per renderla visibile     </td></tr> \n
							<tr><td>${note_hide_tran  }</td><td>la traduzione è nascosta, premi per renderla visibile </td></tr> \n
							<tr><td>${note_show_tran  }</td><td>la traduzione è visibile, premi per nasconderla       </td></tr> \n
						</table>\n
						<table style='font-size:0.5em;width:33%;color:black;border:0px solid black;text-align:left;'>			
							<tr><td style="width:5%;"></td></tr> \n
							<tr><td>
								<input type="range" min="0.25" max="2" value="1" step="0.25" style="width:3em;"> 							
							</td><td>correzione del tempo di inizio o fine della riga</td></tr> \n
							<tr><td></td><td></td></tr> \n
						</table>\n
					</div>
				</div>
			
				<hr>` ; // 
//				
//	document.getElementById("id_symb_meaning").innerHTML = clip_legend;			
//
//--------------------------------------------

	let prototype_tr_m2_tts = ` 
		<tr id="idtr_§1§_m2" style="display:none;background-color:lightgrey;height:1.5em;">
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
			<td class="c_m2"></td>
         </tr>
	` ; // end of prototype_tr_m2_tts

	//--------------------------------
	let prototype_tr_m1_tts = ` 
         <tr id="idtr_§1§_m1" class="playBut1" style="display:none; background-color:lightgrey; border-style: inset;">
            <td class="c_m1"></td>
            <td class="c_m1"></td>
            <td class="playBut1 c_m1"><button class="buttonTD2" id="idb_§1§_m" onclick="onclick_tts_OneClipRow_showHide_sub( this, true)">
               <span style="display:block;font-size:2em;">${openbook_symb}</span>
               <span style="display:none;font-size:2em;">${closedbook_symb}</span></button>
            </td>
            <td class="playBut1 c_m1">
				<button class="buttonTD2" id="idbT_§1§_m" onclick="onclick_tts_OneClipRow_showHide_tran( this, true)">				
					<span style="display:none;font-size:2em;height:1.4em; "><span><span style="font-weight:bold;">${show_translation_symb}</span></span></span>
					<span style="display:block;font-size:2em;height:1.4em;padding:0 0.1em;">
					<span><span style="font-weight:bold;min-width:4em;">${hide_translation_symb}</span></span></span>
				</button>
            </td>
            <td class="c_m1"></td>
            <td class="c_m1"></td>		
			<td class="playBut1 c_m1" >
				<button class="buttonWhite" onclick="onclick_tts_playSynthVoice_m1_row2(this,§1§,false,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span>
				</button>
            </td>
            <td class="playBut1 c_m1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_m1_row2(this,§1§,false,true)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">&plus;</span>
               </button>
            </td>
            <td class="playBut1 c_m1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_m1_row2(this,§1§,true,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">${word_pause_symb}</span>
               </button>
            </td>
			
            <td class="c_m1"></td>
			<td class="c_m1"></td>
         </tr>
	` ; //	end of prototype_tr_m1_tts		 

	//---------------------------------------
	
	let prototype_tr_tts = `		 
         <tr id="idtr_§1§" style="background-color: lightgrey;width:100%;">
            <td class="arrow12"><button class="buttonFromToIx" id="b1_§1§" onclick="onclick_tts_arrowFromIx(this, §1§)">
               <span style="font-size:1em;height:1.4em;">${right_arrow_symb}</span></button>
            </td>
            <td class="arrow12"><button class="buttonFromToIx" id="b2_§1§" onclick="onclick_tts_arrowToIx(  this, §1§)">
               <span style="font-size:1em;height:1.4em;">${left_arrow_symb}</span></button>
            </td>		
            <td class="playBut1">
               <button class="buttonTD2" id="idb_§1§" onclick="onclick_tts_show_row( this, §1§)">
				   <span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span>
				   <span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>
               </button>
            </td>
            <td class="playBut1">
               <button class="buttonTD2" id="idbT_§1§" onclick="onclick_tts_show_row(this, §1§)">
				   <span style="display:none;font-size:2em;height:1.4em; "><span><span style="font-weight:bold;">${show_translation_symb}</span></span></span>
				   <span style="display:block;font-size:2em;height:1.4em;padding:0 0.1em;"><span>
				   <span style="font-weight:bold;min-width:4em;">${hide_translation_symb}</span></span></span>
               </button>
            </td>
            <td class="playBut1">
               <button class="buttonTD2" id="idG_§1§" onclick="onclick_tts_seeWordsGO1(this, §1§)">
					<span style="font-size:2em;height:1.4em;padding:0 0.1em;"><span>${magnifyingGlass_symb}</span></span>
			   </button>
            </td>            
			<td> 
				<div class="divRowText" >
					<div class="suboLine" style="display:none;" id="idp_§1§">§4ptxt§</div>
					<div class="suboLine" style="display:none;" id="idc_§1§">§4txt§</div>
					<div class="tranLine" style="display:none;" id="idt_§1§">§5txt§<br></div>				
					<div id="idw_§1§"></div> 
					<div style="display:none;" id="idtts§1§">§ttstxt§</div>
				</div>
			</td>	
            <td class="playBut1" >
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_row2(this,§1§,false,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span>
               </button>
            </td>
            <td class="playBut1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_row2(this,§1§,false,true)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">&plus;</span>
               </button>
            </td>
            <td class="playBut1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_row2(this,§1§,true,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">${word_pause_symb}</span>
               </button>
            </td>
            <td class="filerow  textfile§nfile§">§1§</td>
			<td class="filerow  textfile§nfile§">§6§</td>
         </tr>
	` ; // end of prototype_tr_tts
//=====================================

let prototype_word_tr_m2_tts = ` 	  
         <tr id="widtr_§1§_m2" style="display:none;background-color:lightgrey;min-height:1.5em;">
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
            <td class="c_m2"></td>
         </tr>
		`; // end of prototype_word_tr_m2_tts

//-----------------------------------------		

let prototype_word_tr_m1_tts = ` 			
         <tr id="widtr_§1§_m1" class="playBut1" style="display:none;background-color:lightgrey;border:1px solid red;">
            <td class="c_m1"></td>
            <td class="c_m1"></td>
            <td class="playBut1 c_m1">
               <button class="buttonTD2" id="widb_§1§_m" onclick="onclick_tts_word_OneClipRow_showHide_sub( this, true, false,true,true)">
                  <span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span>
                  <span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>
			   </button>	  
            </td>
            <td class="c_m1"></td>          
			<td class="c_m1"></td>     			
            <td class="playBut1 c_m1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_m1_row3(this,§1§,false,true)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">&plus;</span>
               </button>
            </td>
            <td class="playBut1 c_m1">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_m1_row3(this,§1§,true,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">${word_pause_symb}</span>
               </button>
            </td>
         </tr>
		`; // end of prototype_word_tr_m1_tts	
		
//--------------------------

let prototype_word_tr_tts = `				
         <tr id="widtr_§1§" style="background-color: lightgrey;">
            <td class="arrow12">
			   <button class="buttonFromToIx" id="wb1_§1§" onclick="onclick_tts_word_arrowFromIx(this, §1§, true, false)">
					<span style="font-size:1em;height:1.4em;">${right_arrow_symb}</span>
			   </button>
            </td>
            <td class="arrow12">
				<button class="buttonFromToIx" id="wb2_§1§" onclick="onclick_tts_word_arrowToIx(  this, §1§, true, false)">
					<span style="font-size:1em;height:1.4em;">${left_arrow_symb}</span>
			   </button>
            </td>
            <td class="playBut1">
               <button class="buttonTD2" id="widb_§1§" onclick="onclick_tts_word_show_row( this, §1§, true, false)">		
					<span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span> 
					<span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>				
               </button>
            </td>
            <td > 
				<div class="suboLine tranTip" style="display:none;" id="widc_§1§">
						§4txt§
				</div>
				<div style="display:none;" id="widtts_§1§">§ttsWtxt§</div>
			</td>
			
			
        
           <td class="playBut1 c_m0" style="width:6em;">
				<div id="widcT_§1§" class="suboLine tranTip" style="display:none;background-color:white;">
						<span class="tranTTxt left1" style="width:250%;z-index:5;"><span style="color:black;">§7txt§</span>§6txt§</span>
				</div>   
		   
            </td>
            <td class="playBut1 c_m0">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_word3(this,§1§,false,true)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">&plus;</span>
               </button>
            </td>
            <td class="playBut1 c_m0">
               <button class="buttonWhite" onclick="onclick_tts_playSynthVoice_word3(this,§1§,true,false)">
					<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span><span style="font-size:0.9em;">${word_pause_symb}</span>
               </button>
            </td>    
         </tr>
 		`; // end of prototype_word_tts	

//------------------------------------

	let string_tr_m2 = `		
		<tr id="idtr_§1§_m2"  style="display:none;background-color:white;height:1.5em;" > 
			<td></td><td></td><td></td><td></td><td></td><td></td>
			<td></td><td></td><td></td>
			<td></td> 
		</tr> `; // end  str_td_m2_last6
	
	//----------------------------------------------
	let str_tr_m1_zero = `
		<tr id="idtr_§1§_m1"  class="playBut1" style="display:none;background-color:lightgrey; border-style: inset;">
			<td class="c_m1"></td>
			<td class="c_m1"></td>		
			<td class="playBut1 c_m1"><button class="buttonTD2" id="idb_§1§_m" 
				onclick="onclick_tts_OneClipRow_showHide_sub( this, true)">
				<span style="display:block;font-size:2em;">${openbook_symb}</span>
				<span style="display:none;font-size:2em;">${closedbook_symb}</span></button>
			</td>  
						
			<td class="playBut1 c_m1"><button class="buttonTD2" id="idbT_§1§_m" 
				onclick="onclick_tts_OneClipRow_showHide_tran( this, true)">				
				<span style="display:none;font-size:2em;height:1.4em; "><span>${show_translation_symb}</span></span>
				<span style="display:block;font-size:2em;height:1.4em;padding:0 0.1em;">
				<span>${hide_translation_symb}</span></span></button>
			</td>  	
			<td class="c_m1"></td>
			<td class="c_m1"></td>
		`; // end string_tr_fant_m1

	//----------------------------
	let str_td_m1_playVideo = `				
			<td class="playBut1 c_m1" ><button class="buttonTD2" id="sp§1§_no1" onclick="onclick_tts_playVideo_m1_row(this)">
				<span style="font-size:2em;">${speakinghead_symb}</span></button>
			</td>  
		`; // end str_td_m1_playVideo 	
	//---------------------
	let str_td_m1_playVideoLoop = `
			<td class="playBut1 c_m1">
					<button class="buttonTD2" id="sp§1§_ye1" onclick="onclick_tts_playVideo_m1_rowLoop(this)" style="font-size:1.0em;">${playLoop_symb}</button>
			</td> 	
		`; // end str_td_m1_playVideoLoop	
	//---------------------
		let str_td_m1_insertPause = `	
			<td class="playBut1 c_m1"></td> 
			` ; // end str_td_xx__insertPause 	
	//-----------	
	let str_td_m1_last6 = `		
			<td class="c_m1"></td>	
		</tr> `; // end  str_td_m1_last6	
		
	//-------------------------
	let string_tr_m1 = "";		
	let string_tr_m1_pre_voices  = str_tr_m1_zero.trim() + 
					str_td_m1_insertPause.trim() +
					"\n" ;
					//"\n"+ str_td_m1_playVideo.trim() + "\n" + 
					//str_td_m1_playVideoLoop.trim() + "\n" ; 
					
	let string_tr_m1_post_voices =  str_td_m1_playVideoLoop.trim() + 
					str_td_m1_last6.trim();


	//---------------------
	/***
	//  tr_xx  td_xx   xx instead of _m1_  or _m2_
	let str_tr_xx_1 = ` 
		<tr id="idtr_§1§" style="background-color: lightgrey;width:101%;"> 	
			<td class="arrow12"><button class="buttonFromToIx" id="b1_§1§" onclick="onclick_tts_arrowFromIx(this, §1§)">
				<span 	style="font-size:1em;height:1.4em;">→</span></button>
			</td>  
			<td class="arrow12"><button class="buttonFromToIx" id="b2_§1§" onclick="onclick_tts_arrowToIx(  this, §1§)">
				<span style="font-size:1em;height:1.4em;">←</span></button>
			</td>  		
			<td class="playBut1">
				<button class="buttonTD2" id="idb_§1§" onclick="onclick_tts_show_row( this, §1§)">
					<span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span>
					<span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>
				</button>
			</td> 		
			<td class="playBut1">
				<button class="buttonTD2" id="idbT_§1§" onclick="onclick_tts_show_row(this, §1§)">
					<span style="display:none;font-size:2em;height:1.4em; "><span>${show_translation_symb}</span></span>
					<span style="display:block;font-size:2em;height:1.4em;padding:0 0.1em;"><span>${hide_translation_symb}</span></span>
				</button>
			</td>  					
			<td class="playBut1">
				<button class="buttonTD2" id="idG_§1§" onclick="onclick_tts_seeWordsGo2(this, §1§)">
					<span style="font-size:2em;height:1.4em;padding:0 0.1em;"><span>${magnifyingGlass_symb}</span>
				</button>
			</td>
			
			<td > 
				<div class="divRowText" >
					<div class="suboLine" style="display:none;" id="idp_§1§">§4ptxt§</div>
					<div class="suboLine" style="display:none;" id="idc_§1§">§4txt§</div>					
					<div class="tranLine" style="display:none;" id="idt_§1§">§5txt§<br></div>				
					<div id="idw_§1§"></div> 
					<div style="display:none;" id="idtts§1§">§ttstxt§</div>
				</div>
			</td>	
				`; // end   str_tr_xx_1
			
	//---------------------			
	let str_td_xx__playVideo = `			
			<td class="playBut1">
				<button class="buttonTD2" id="sp§1§" onclick="onclick_tts_playVideo_row(this, §1§)">
				<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span>
				</button>
			</td>    
			` ; // end str_td_xx__playVideo
		
	//-------		
	let str_td_xx__playVideoLoop = `		
			<td class="playBut1">
				<button class="buttonTD2 " onclick="onclick_tts_playVideo_rowLoop(this,§1§)" style="font-size:1.0em;">${playLoop_symb}
				</button>
			</td>   
			` ; // end str_td_xx__playVideoLoop
	//--------		
	let str_td_xx__playTTS_Loop = `		
			<td class="playBut1">
				<button class="buttonTD2 " onclick="onclick_tts_playTTS_rowLoop(this,§1§)" style="font-size:1.0em;">${playLoop_symb}
				</button>
			</td>   
			` ; // end str_td_xx__playTTS_Loop()		
	//------------------				
	let str_td_xx__insertPause = `	
			<td class="playBut1">
				<button class="buttonWhite" onclick="onclick_tts_interWordPause(this,§1§)" style="font-size:0.9em;">&#x1d110;
				</button>
			</td> 
			` ; // end str_td_xx__insertPause 	
	//-----------
	let str_td_xx__last5col = `		
			<td class="timerow1">§1§</td>
		</tr> 
		`; // end let str_td_xx__last5col;
	//----------------------


	let string_tr_xx = "";		
	let string_tr_xx_pre_voices  = str_tr_xx_1.trim() + "\n"+ 
		str_td_xx__insertPause.trim() + "\n" + 
		""; 

	let string_tr_xx_post_voices =  str_td_xx__playTTS_Loop.trim() + "\n"  + 			
				'<td class="timerow1">§1§</td>'				
				"</tr> \n"; 
				
	//------------------------
	****/
	let string_tr_xx = "";		
	
			
let word_tr_fant = `
		<tr id="widtr_§1§_m2"  style="display:none;background-color:lightgrey;height:1.5em;" > 
			<td></td><td></td><td></td><td></td>
			§table_voices_m2§
		</tr> \n 		

		<tr id="widtr_§1§_m1"  class="playBut1" style="display:none;background-color:lightgrey; border-style: inset;">
			<td class="c_m1"></td>
			<td class="c_m1"></td>		
			<td class="playBut1 c_m1"><button class="buttonTD2" id="widb_§1§_m" onclick="onclick_tts_word_OneClipRow_showHide_sub( this, true, false,true,true)">
				<span style="display:none; font-size:2em;">${openbook_symb}</span>
				<span style="display:block;font-size:2em;">${closedbook_symb}</span></button>
			</td>  	
			<td class="c_m1"></td>
			§table_voices§
			
			</tr> \n  
	` ; // 		

//-------------------------
// XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
let word_tr_allclipOLD = ` 
		<tr id="widtr_§1§" style="background-color: lightgrey;"> 	
			<td class="arrow12"><button class="buttonFromToIx" id="wb1_§1§" onclick="onclick_tts_word_arrowFromIx(this, §1§, true, false)">
				<span 	style="font-size:1em;height:1.4em;">→</span></button>
			</td>  
			<td class="arrow12"><button class="buttonFromToIx" id="wb2_§1§" onclick="onclick_tts_word_arrowToIx(  this, §1§, true, false)">
				<span style="font-size:1em;height:1.4em;">←</span></button>
			</td>  		
			<td class="playBut1">
				<button class="buttonTD2" id="widb_§1§" onclick="onclick_tts_word_show_row( this, §1§, true, false)">
					<span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span> \n
					<span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>
				</button>
			</td> 		
			<td > 
				<div class="suboLine" style="display:block;visibility:hidden;" id="widc_§1§">§4txt§</div>
				<div style="display:none;" id="widtts_§1§">§ttsWtxt§</div>
			</td>			
			§table_voices§			
			</tr> \n  
	` ; // end of word_tr_allclip 
//-----------------------------
	let word_tr_allclip = ` 
		<tr id="widtr_§1§" style="background-color: lightgrey;"> 	
			<td class="arrow12"><button class="buttonFromToIx" id="wb1_§1§" onclick="onclick_tts_word_arrowFromIx(this, §1§, true, false)">
				<span 	style="font-size:1em;height:1.4em;">→</span></button>
			</td>  
			<td class="arrow12"><button class="buttonFromToIx" id="wb2_§1§" onclick="onclick_tts_word_arrowToIx(  this, §1§, true, false)">
				<span style="font-size:1em;height:1.4em;">←</span></button>
			</td>  		
			<td class="playBut1">
				<button class="buttonTD2" id="widb_§1§" onclick="onclick_tts_word_show_row( this, §1§, true, false)">
					<span style="display:none;font-size:2em;height:1.4em;">${openbook_symb}</span> \n
					<span style="display:block;font-size:2em;height:1.4em;">${closedbook_symb}</span>
				</button>
			</td> 		
			<td > 
				<div class="suboLine tranTip" style="display:block;visibility:hidden;" id="widc_§1§">
						§4txt§
				</div>
				<div style="display:none;" id="widtts_§1§">§ttsWtxt§</div>
			</td>
			
			§table_voices§			
			</tr> \n  
	` ; // end of word_tr_allclip
//-----------------------------