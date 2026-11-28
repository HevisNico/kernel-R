# Suivi (coordinateur) — décisions du propriétaire à reporter dans l'amendement

## Reporté après la répétition 2
- L1 : rejeu tiers a posteriori de la vérification du scan, à partir des SHA (les branches auront bougé).
  - Prérequis conservés dès maintenant : les deux inventaires nom -> SHA (VERIFY_LSREMOTE.txt, SCAN_LSREMOTE.txt),
    les sha256 du code de scan (draw_seeds.py, analysis.py), le commit F du gel, les sha256 des deux sorties de scan.
  - Le rejeu dépendra aussi de la disponibilité des objets Git correspondants (tips récupérables par SHA).

## Formulations pour l'amendement
- Garantie F1 : la reproduction du scan à partir des branches publiques est OBLIGATOIRE avant l'annonce de campagne.
  Ce qui est reporté est le rejeu par un tiers après coup. D'ici là, un tiers contrôle le rapport publié
  (evidence/combined-scan-verify), son contenu et sa date de création GitHub (strictement antérieure à l'annonce).
- Le scan publié est reproductible à partir d'un état public du dépôt observé avant l'annonce. Les exclusions de la
  liste finale ont deux origines vérifiables : le scan, et les tirages des répétitions selon la règle écrite
  (graines et graines de bruit 10S+0..3, qui n'apparaissent pas forcément littéralement).
- Indépendance matérielle des deux exécutions : propriété de la procédure, pas des fichiers.
- L2 : les traces publiées (run_9219986b_*, futur rapport) contiennent des entiers que le scan suivant exclura
  par construction (88 entiers, 5 nouveaux mesurés). Conservateur, traçable.
- §3 : la liste rescannée sur dev à 9219986b (CLONE_HEAD), par rescan.sh (PART 1 = [block second-scan] verbatim),
  reproduite à l'octet près par un second scan indépendant, enregistrée en e38b4df3 (a3a76e1a, 16333 entiers, 286 refs).
- §2 : suite 52/52 à e38b4df3 sur deux machines (dev/equiv/DEFECTS_AT_e38b4df3_K02.json, _checker.json) — à refaire
  sur le SHA final.
- (c) 29/30 à f46c49e0 (pas 28/29 ; erratum e1c870d4).
- Essai isolé : le cas exact_union de (c) lancé en avance par le vérificateur sur 13ebca8b — ne compte pas dans le
  bilan de (c), qui portera sur le SHA final.

## Critère de clôture du dernier ajout (lecture du rapport public)
Sur le candidat complet : rapport absent / autre hash / verdict non succès -> refus avant tout commit ou push
d'annonce ; témoin honnête -> passe ; analysis.py refuse rapport créé après l'annonce et second commit sur la branche.
