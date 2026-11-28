# ÉTAT DU COORDINATEUR (session_01TzF7ZUoTUj44AGYGuEFzHA) — 2026-11-28 ~11:00 UTC
Parler FRANÇAIS au propriétaire (Nicolas Breuillaud). Rigueur > vitesse. Il décide chaque étape sortante.
Voir aussi SUIVI.md (décisions pour l'amendement, L1 reporté, critère de clôture).

## Règles permanentes
- Commits : auteur ET committer = le propriétaire (env GIT_AUTHOR_*/GIT_COMMITTER_* depuis main), sujet seul, AUCUN trailer.
- Jamais force-push, jamais supprimer/réécrire une branche distante, jamais merger. Fetch par NOM de branche, jamais clone complet (~23 Go d'evidence).
- GEL DES PUSHS en vigueur sur toutes les branches ; levé ponctuellement par le propriétaire, push par push.
- Toujours dire le type d'empreinte : commit / blob / « sha256 du fichier ». Vérifier sur GitHub avant d'affirmer.
- La session implémenteur exige l'accord DIRECT du propriétaire dans SA session pour pousser (permission system).
- Ne pas fusionner PR #190 (avis donné : attendre gel + amendement + répétition 2).

## Sessions
- Implémenteur : session_01TzF7ZVGjZjJcvQGoXk8dXp (« kernel-R: exact-union fix (implementer) »). Repo attaché push.
- Vérificateur/relecteur indépendant (« nouveau worker ») : session_01TzF7ZVyj98nLkaSRd4xWXB. Chaîne figée installée ; /home/user/rescan_work (scan complet 22 Go, garder) ; 34 Go libres.
- Rédacteur de tests indépendant : session_01TzF7ZTyrHCbSzqfjfwMyQW. Ne voit pas le code, seulement l'interface que je relaie.
- K02 (exécutant) : session_01TzF7ZUzWF9YA9phr9ZxG8C. ~/runner/ (à effacer entièrement à la fin, + CREATED.txt : ~/.cache/pip, attrib.py dans son scratchpad). 52 Go libres. ~/reh/out_K02 à garder.
- Ancien worker session_01TzF7ZYVsvGaQ6EzEjxCJLM : SATURÉ, NE PLUS UTILISER. Ancien coordinateur session_01TzF7ZYZVxJcErqniRxMQ4F (audite à la demande du propriétaire).
- Machines K01, K03–K12 : inactives (répétition 2 seulement).

## Branches (vérifiées)
- research/layered-campaign-dev = 13ebca8b (pushé, vérifié : 114/114 pins, FREEZE_PINS adb62966, analysis.py 013f01ac seul pin changé depuis e38b4df3).
  Historique : 0ce2d1af → 030e6bd9/9219986b (rescan.sh) → e38b4df3 (liste rescannée, pins) → 1d9d8394 (trace K02 + suite K02) → da3d9b3b (trace vérificateur + suite) → 72013e13/a5ba132b (union exacte) → 372573e8/fe82ec0a/46e08e09/13ebca8b (/2, check_scan, verify-scan…).
- Gel actuel : research/layered-campaign-freeze = 5d02acce (inchangé). Prédiction 0e15bb14. PR #190 ouverte.
- evidence/combined-rehearsal1-local-records = e1c870d4 (erratum 29/30 sur dd672b12).
- Rescan final : EXCLUDED.json a3a76e1a…, EXCLUDED_PRINT efc8d463…, 16333 entiers, 286 refs, reproduit à l'octet par 2 machines.

## FAIT — f20b3d8b PUSHÉ et VÉRIFIÉ par moi (114/114 pins, seul pin changé = analysis.py 069eeca8, identité propriétaire, 0 trailer, fast-forward 13ebca8b..f20b3d8b). Lancés : rédacteur de tests (71 cas sur f20b3d8b), vérificateur (revue #3, lecture seule). ATTENDRE leurs rapports.
## (ancien) rapport final reçu 12:06Z : f20b3d8bc9c8a9a79966badd97a0d368e48fad86 complet, local ; (c) 35/35, suite 52/52, (a) 24/24 ; relu par moi, OK ; attend push autorisé par le propriétaire DANS la session implémenteur
- Commits sur 13ebca8b : 82dd9260, a4c9e9c2 (lecture du rapport scan_verify_record / check_scan_verify), 2530adda (N1,N2), 0376d136 (pins), f20b3d8b (VERIFY_INPUTS.txt).
- FREEZE_PINS.json dcf1a676…, analysis.py 069eeca8…. f20b3d8b ne touche aucun pin.
- L'implémenteur fait tourner : suite (52), (a) (24), (c) complet. J'attends son rapport (diffs vs 13ebca8b + résultats).
- Rédacteur de tests : 71 cas, 60/71 à 13ebca8b, 11 attendent f20b3d8b.

## PROCHAINES ÉTAPES
1. Recevoir le rapport final de l'implémenteur ; relire diffs ; demander au propriétaire d'autoriser le push de f20b3d8b DANS la session implémenteur.
2. Vérifier le push sur GitHub (pins 114/114, identité, pas de trailer). Lancer : rédacteur de tests (71 cas), vérificateur (revue #3).
3. Critère de clôture (SUIVI.md) doit passer sur le SHA final.
4. Puis : STATUS de FREEZE.txt + ligne suite (« 51 of 51 at 8bac22cc » → 52/52 sur SHA final), un seul proof2 (≈ 2 scans, ~50 Go : K02 trop juste à 52 Go → proposer de libérer le scanrepo du vérificateur 22 Go et lancer chez lui, ou autre), puis (c) complet sur SHA final.
5. Vérification depuis un clone neuf, amendement 1 (brouillon dans le message système initial + SUIVI.md), push du gel, amendement seul, commentaire PR #190, répétition 2 (budget tokens du propriétaire, avant mercredi si possible).
6. À la fin : K02 efface ~/runner et CREATED.txt (garder ~/reh/out_K02).

## Revue #3 reçue 12:37Z (vérificateur) — critère de clôture TIENT ; N1/N2 corrigés ; pins 114/114 regénérés à l'octet
- M1 MEDIUM : seule la dernière ligne de VERIFY.txt est lue ; VERIFY_INPUTS/VERIFY_LSREMOTE/SCAN_LSREMOTE jamais recoupés (analysis.py:1772-1813 ; FREEZE.txt:634-639).
- L1 : succès précédé de lignes PROBLEM accepté. L2 : bloc announce ne vérifie pas l'historique/date du rapport (seul analysis.py, après coup). L3 : identité du commit rapport non vérifiée (info). L4 : VERIFY_INPUTS sans version git/python, F vide non refusé. I1 info.
- proof2 n'exerce pas la partie activité de check_scan_verify -> à couvrir par (c).
- En attente : décision propriétaire sur M1/L1/L2/L4 ; rapport rédacteur de tests (71 cas).

## 12:45Z Décision propriétaire : corriger M1, L1, L2, L4 avant gel (L3 inchangé). Envoyé à l'implémenteur (local, pas de push).
- Lecteur unique (bloc announce + analysis.py), 4 fichiers même commit, aucun PROBLEM, recoupement HS / SHA gel complet attendu / pins code / sha des inventaires ; inventaires nom+SHA comparés hors ligne.
- L2 : avant 1er commit d'annonce, GitHub : branche créée au commit lu + usage unique ; après : analysis.py refait + compare les 2 heures de création (antériorité stricte).
- L4 : versions git/python ; F == SHA complet attendu (vide ou différent refusé).
- Revue #4 ciblée : (1) rapport réduit à 1 ligne, (2) dossier complet citant un autre gel, (3) inventaire bon nom mauvais SHA -> refus avant commit d'annonce ; authentique passe. + cas branche remise sur commit initial après mouvement interdit.
- Décision du gel : suite complète + (a) sur SHA final avec empreintes recalculées, puis revue courte du diff. Les 71 cas sur f20b3d8b = intermédiaire.
- Rédacteur de tests : autorisé commit LOCAL de correction de fixtures (5 cas), relance 71.
- 12:40Z rédacteur : 71/71 sur f20b3d8b (intermédiaire), fixtures commit local ac5b7aa8, fichier test sha256 4b1a8bb3. Prêt à relancer sur SHA final (ajouter cas M1/L1/L2/L4 une fois l'interface relayée).

## 12:52Z Implémenteur : M1/L1/L2/L4 FAIT, LOCAL. b6605c76 (lecteur partagé) + 7fa3693e (pins). Distant = f20b3d8b.
- FREEZE_PINS 6b9704cf…, analysis.py 0c10b8b9… (seul pin changé). Suite 52/52, (a) 24/24, cas (c) touchés 7/7 (scan_verify_record 37 contrôles). (c) complet et proof2 NON lancés.
- Interface : scan_verify_record(remote, hs, scan_bytes, freeze, branch) ; record_created ; record_activity (twin = <remote>/ACTIVITY/<branch__>.json si remote non github.com) ; check_scan_verify(hs, announce_push_utc, outdir, scan_bytes, freeze) ; inventory_problems.
- Point à faire vérifier en revue #4 : le chemin « jumeau » de record_activity ne doit jamais être atteignable en production (remote littéral GitHub dans le bloc et verify_remote()).
- Prochaine étape : propriétaire autorise push 7fa3693e DANS la session implémenteur -> je vérifie -> revue #4 (vérificateur) + rédacteur de tests.

## 12:58Z 7fa3693e PUSHÉ (accord direct propriétaire chez l'implémenteur) et VÉRIFIÉ par moi : avance f20b3d8b..7fa3693e, 2 commits, identité OK, 0 trailer, 114/114 pins, seul pin changé analysis.py 0c10b8b9, FREEZE_PINS 6b9704cf, même ensemble.
- Lancés : revue #4 (vérificateur, cas 1-8 dont chemin jumeau inatteignable), rédacteur de tests (nouvelle interface + cas 1-6 + témoins).
- Ensuite : décision gel = suite + (a) sur SHA final + revue courte ; puis STATUS/ligne suite, proof2, (c) complet, clone neuf, amendement…

## 13:10Z Audit (session_01TzF7ZY6r5bQSdPJAj3AWYB, ouverte par le propriétaire, lecture seule) : 8 questions, répondu.
- POINT OUVERT NOUVEAU : 61 entiers (règle draw_seeds) sur la pointe dev 7fa3693e hors EXCLUDED.json (0 à 9219986b) ; 55 dans [10000,100000). Campagne couverte par le second scan ; RÉPÉTITION 2 exposée (liste = frz ∪ rép.1). « rescanned LAST » plus exact. À décider par le propriétaire : rescan final après dernier commit, ou amendement.
- Autres non décidés relevés : publier l'attente G3 K0 avant tirage ; parade redémarrage (prévention) ; conteneur récupéré avant publication des racines ; mention règle identité dans rapport final ; bilan §9 (coûts, marges, machines) non compilé.
- Brouillon amendement 1 : dans scratchpad/brief_initial.txt (l. 98+), §3 périmé (4 fichiers), manque /2, union exacte, verify-scan, lecteur rev #3.

## 13:15Z Revue #4 reçue : cas du propriétaire 1-6 et 8 TOUS refusés avant commit, authentique passe (A analysis + B bloc verbatim). Pins 114/114, régénération identique 6b9704cf.
- L1 LOW : verify_scan ne vérifie pas VERIFY_INPUTS ; versions seulement non vides (enregistrées, pas comparées). Ne pas le citer comme « vérifié ».
- L2 LOW (préexistant, toutes lectures GitHub) : redirection possible par config git (insteadOf via ~/.gitconfig, GIT_CONFIG_GLOBAL, GIT_CONFIG_COUNT/KEY/VALUE) et GH_HOST pour gh api. ATTENTION : nos conteneurs utilisent eux-mêmes GIT_CONFIG_COUNT/KEY/VALUE (insteadOf ssh->https) et ~/.gitconfig (proxyauth) -> une parade « GIT_CONFIG_GLOBAL=/dev/null » peut casser l'accès ; à étudier.
- I1 : 5e fichier dans le rapport accepté. I2 : API d'activité en retard -> refus « no activity » (échec fermé).
- PROPRIÉTAIRE 13:15Z : « On attend la fin de l'audit » -> NE RIEN LANCER. En attente aussi : rédacteur de tests sur 7fa3693e ; décision A/B rescan liste (61 entiers).
- 13:04Z rédacteur : 90/90 sur 7fa3693e (commit local aad8aa09, test sha256 2b06d9be), tous les cas du propriétaire passent des deux côtés. Toujours : on attend la fin de l'audit.

## 13:10Z DÉCISION RELAYÉE PAR L'AUDIT (à faire confirmer par le propriétaire ICI) : STOP marche vers le gel ; publier proprement tout dans une PR prête (pas fusionnée) ; puis travail XOR ; puis nouvelle préparation de campagne. Retrait public daté avant tout tirage ; rien supprimé ; graines utilisées restent exclues ; nouvelle prédiction XOR validée sur nouvelles graines de dev.
- Faits : PR #190 head = research/layered-campaign-prediction 0e15bb14, base main 3f27bb36. dev 7fa3693e contient main + gel 5d02acce mais PAS la branche prediction. 118 commits main..dev.
- Rien lancé. Questions posées au propriétaire : PR nouvelle vs #190 ; branche source ; note de retrait seule sur prediction ; sessions/commits locaux (test writer aad8aa09) ; NOT1/ANDOR3 attendent XOR ?
## 13:12Z Audit relaie 2e décision : même PR #190, note de retrait EN TÊTE ; sessions stoppées, commits locaux abandonnés ; NOT1/ANDOR3 attendent XOR ; texte du point d'arrêt fourni (+2 précisions proposées par l'audit). À FAIRE CONFIRMER ICI. Hors git qui partirait : tests rédacteur (aad8aa09, 90 cas), brouillons K02 51e13e16/c44f3a9b, étage D 071ba6c/4fcd90a/d83ee5f, mes ETAT/SUIVI/brouillon amendement.
## 13:15Z Audit relaie 3e décision (REMPLACE « on les oublie ») : archiver AVANT fermeture les lots a (rédacteur tests), b (K02 51e13e16,c44f3a9b), c (étage D 071ba6c,4fcd90a,d83ee5f — session ANCIEN WORKER saturé !), d (moi : brouillon amendement « brouillon non adopté » + ETAT/SUIVI), e (fichiers non commités : revues #3/#4, sorties suites, journaux). Fiche par lot (provenance, état, où) + SHA256SUMS ; vérif par l'audit dans clone neuf ; fermer une session seulement après verdict. Passage final XOR fourni (remplace 2 phrases). Cadre reprise XOR à consigner. EN ATTENTE CONFIRMATION PROPRIÉTAIRE ICI.
