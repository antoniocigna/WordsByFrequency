Words By Frequency
------------------ 
Antonio Cigna 2023  
  
**attenzione work in progress ( manca documentazione e traduzione dei messaggi)**  
  
Questa applicazione (che funziona soltanto su desktop windows) si propone come uno strumento per migliorare la comprensione di una lingua straniera.  
Legge un file di testo anche di grande dimensioni ( provato anche con 100 mila righe)  
Estrae tutte le frasi e le parole  
  
Se esiste, legge un file che associa ad ogni parola un o più lemma (cioè il termine che si cerca in un dizionario)  
E' possibile richiedere:
*   la lista delle parole più frequenti (tutte le parole esistenti sono ordinate in ordine decrescente di utilizzo (prima le più usate)
*   la lista delle parole con lo stesso prefisso
*   la lista delle parole con lo stesso lemma
  
Per ogni parola listata è possibile leggere la traduzione (spostando il mouse) o listare le frasi del testo che la contengono  

E' inoltre possibile listare
*   tutte le frasi che contengono una certa parola
*   tutte le frasi in sequenza di apparizione nel testo

  
E' possibile richiedere la lettura con una voce sintentica di ogni parola e di ogni frase  

**Software**
*   Start.bat               - un file per chiamare il file exe   
*   wordsByFrequency.exe    - legge i file ed esegue tutto il lavoro pesante ( il programm è scritto in linguaggio **go** )    
*   wordByFrequency.html,   wordByFrequency.js e altri file html/javascript  ( per gestire le richieste dell'utente )   
  
    
**Antonio Cigna**  
16 Ottobre 2023  