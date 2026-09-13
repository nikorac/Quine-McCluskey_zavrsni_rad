#  Pomoćne funkcije

def count_ones(s: str) -> int:
    """Vraća broj '1' znakova u binarnom stringu (mintermu)."""
    count = 0
    for c in s:
        if c == '1':
            count += 1
    return count

def differ_by_one_bit(a: str, b: str):
    """
    Provjerava razlikuju li se dva binarna stringa u točno jednom bitu.
    Vraća indeks tog bita, ili None ako se razlikuju na više mjesta ili na poziciji '-'.
    """
    diff_count = 0
    diff_pos = -1
    for i in range(len(a)):
        if a[i] != b[i]:
            if a[i] == '-' or b[i] == '-':
                return None
            diff_count += 1
            diff_pos = i
            
    if diff_count == 1:
        return diff_pos
    return None

def merge_terms(a: str, b: str) -> str:
    """
    Spaja dva binarna stringa u jedan tako da na poziciji razlike stavlja '-'.
    Baca ValueError ako se stringovi razlikuju na više od jednog mjesta.
    """
    pos = differ_by_one_bit(a, b)
    if pos is None:
        raise ValueError("Termini se ne mogu spojiti.")
    
    result = ""
    for i in range(len(a)):
        if i == pos:
            result += '-'
        else:
            result += a[i]
    return result

def int_to_bin(n: int, num_vars: int) -> str:
    """Pretvara cijeli broj n u binarni string duljine num_vars."""
    result = ""
    temp = n
    for i in range(num_vars):
        if temp % 2 == 1:
            result = "1" + result
        else:
            result = "0" + result
        temp = temp // 2
    return result

def term_to_expression(term: str, variables: list[str]) -> str:
    """
    Pretvara binarni string termina u algebarski izraz (npr. 10-1 -> AB'D).
    Vraća '1' ako je term složen samo od '-' znakova (tautologija).
    """
    result = ""
    for i in range(len(term)):
        if term[i] == '1':
            result += variables[i]
        elif term[i] == '0':
            result += variables[i] + "'" # "\u0305" za overline
    
    if len(result) == 0:
        return "1"
    return result

def find_prime_implicants(minterms: list[int], dont_cares: list[int], num_vars: int):

    def make_initial_groups():
        """
        Grupira sve početne minterme i don't care uvjete u dvodimenzionalnu listu 
        na temelju broja jedinica u njihovom binarnom zapisu.

        Returns:
            list[list[tuple[str, list[int]]]]: Dvodimenzionalna lista težinskih grupa.
            
            Primjer izgleda strukture za 3 varijable (minterms=[1, 2, 3], dont_cares=[0]):
            [
                [ ('000', [0]) ],               # Grupa 0 (0 jedinica) -> pokriva izraz (dont care ili mintrm) 0
                [ ('001', [1]), ('010', [2]) ], # Grupa 1 (1 jedinica) -> pokriva izraze 1 i 2
                [ ('011', [3]) ],               # Grupa 2 (2 jedinice) -> pokriva izraz 3
                []                              # Grupa 3 (3 jedinice - prazna)
            ]
        """
        groups = []
        for _ in range(num_vars + 1):
            groups.append([])
        all_terms = minterms + dont_cares
        for m in all_terms:
            term_str = int_to_bin(m, num_vars)
            groups[count_ones(term_str)].append((term_str, [m]))
        return groups

    def groups_are_empty(groups):
        """Vraća True ako su sve težinske grupe prazne, što označava kraj algoritma."""
        for g in groups:
            if len(g) > 0:
                return False
        return True

    def print_groups(groups):
        """Ispisuje sve termine trenutne generacije sortirane po najmanjem mintermu."""
        current_flat = []
        for g in groups:
            for item in g:
                current_flat.append(item)
        current_flat.sort(key=lambda x: min(x[1]))

        print(f"Termini ({len(current_flat)}):")
        for term_str, mints in current_flat:
            real_mints = sorted([x for x in mints if x in minterms])
            used_dcs   = sorted([x for x in mints if x in dont_cares])
            if len(used_dcs) > 0:
                print(f"  {term_str}  ←  mintermi {real_mints}  (don't cares {used_dcs})")
            else:
                print(f"  {term_str}  ←  mintermi {real_mints}")

    def try_merge(a_str, a_mints, b_str, b_mints):
        """
        Pokušava sažeti dva izraza ako se razlikuju u točno jednom bitu, 
        vraćajući novi binarni niz s crticom i uniju pokrivenih minterma (combined) ili None ako spajanje nije moguće.
        """
        if differ_by_one_bit(a_str, b_str) is None:
            return None
        merged_str = merge_terms(a_str, b_str)
        combined = list(a_mints)
        for m in b_mints:
            if m not in combined:
                combined.append(m)
        return (merged_str, combined)

    def compute_next_groups(groups):
        """
        Generira sljedeću generaciju težinskih grupa spajanjem kompatibilnih izraza iz susjednih grupa.

        Uspoređuje elemente svake težinske grupe i s elementima grupe i+1. Ako se dva izraza 
        razlikuju u točno jednom bitu, sažima ih u novi izraz, smješta ga u odgovarajuću grupu 
        nove generacije te bilježi koordinate iskorištenih izraza kako ne bi postali primarni implikanti.

        Parameters:
            groups (list[list[tuple[str, list[int]]]]): Dvodimenzionalna lista trenutne generacije 
                gdje je svaki element par (binarni_string, lista_pokrivenih_minterma).

        Returns:
            tuple[list[list[tuple[str, list[int]]]]], set[tuple[int, int]]]: 
                - next_groups: Dvodimenzionalna lista nove generacije implikanata.
                - used: Skup koordinata (indeks_grupe, indeks_unutar_grupe) iskorištenih izraza.

        Primjer izvođenja:
            Ulaz groups:
            [
                groups[0] = [ ('000', [0]) ]
                groups[1] = [ ('001', [1]), ('010', [2]) ]
            ]
            Izlaz next_groups:
                next_groups[0] = [ ('00-', [0, 1]), ('0-0', [0, 2]) ]
            Izlaz used:
                { (0, 0), (1, 0), (1, 1) }
        """
        next_groups = []
        for _ in range(num_vars + 1):
            next_groups.append([])

        used     = set()
        seen_str = set()

        for i in range(len(groups) - 1):
            if len(groups[i]) == 0 or len(groups[i + 1]) == 0:
                continue
            for a in range(len(groups[i])):
                for b in range(len(groups[i + 1])):
                    result = try_merge(groups[i][a][0], groups[i][a][1],
                                       groups[i+1][b][0], groups[i+1][b][1])
                    if result is not None:
                        merged_str, combined = result
                        if merged_str not in seen_str:
                            seen_str.add(merged_str)
                            next_groups[count_ones(merged_str)].append((merged_str, combined))
                        used.add((i, a))
                        used.add((i + 1, b))

        return next_groups, used

    def collect_unused(groups, used):
        """
        Izdvaja sve implikante iz trenutne generacije koji nisu sudjelovali u spajanju 
        jer oni predstavljaju maksimalno sažete primarne implikante.
        """
        unused = []
        for i in range(len(groups)):
            for j in range(len(groups[i])):
                if (i, j) not in used:
                    unused.append(groups[i][j])
        return unused

    def covers_real_minterm(pi):
        """
        Provjerava pokriva li primarni implikant barem jedan stvarni minterm 
        (isključujući isključivo 'don't care' uvjete).
        """
        for m in pi[1]:
            if m in minterms:
                return True
        return False

    # ── Glavna petlja ────────────────────────────────────────────────────────

    groups = make_initial_groups()
    prime_implicants = []
    iteration = 0

    while not groups_are_empty(groups):
        iteration += 1
        print(f"\n--- Iteracija {iteration} ---")
        print_groups(groups)

        next_groups, used = compute_next_groups(groups)
        prime_implicants += collect_unused(groups, used)
        groups = next_groups

    return [pi for pi in prime_implicants if covers_real_minterm(pi)]

def build_prime_implicant_chart(minterms: list[int], prime_implicants: list, variables: list[str]) -> None:
    """
    Ispisuje tablicu primarnih implikanata u konzolu.

    Args:
        minterms: lista minterma funkcije
        prime_implicants: lista tuplova (binarni_string, lista_minterma)
        variables: lista imena varijabli (npr. ['A', 'B', 'C', 'D'])
    """

    def calculate_widths():
        col_w = 0
        for m in minterms:
            if len(str(m)) > col_w:
                col_w = len(str(m))
        col_w += 2

        label_w = 0
        for term, covered in prime_implicants:
            expr_len = len(term_to_expression(term, variables))
            if expr_len > label_w:
                label_w = expr_len
        label_w += 2

        title_cov = "Pokriveni mintermi"
        cov_w = len(title_cov)
        for term, covered in prime_implicants:
            cov_str = ", ".join(str(x) for x in sorted(covered))
            if len(cov_str) > cov_w:
                cov_w = len(cov_str)
        cov_w += 2

        return col_w, label_w, cov_w

    def build_header(col_w, label_w, cov_w):
        title_cov = "Pokriveni mintermi"
        header = " " * label_w + "|"
        for m in minterms:
            header += str(m).center(col_w) + "|"
        header += title_cov.center(cov_w)

        sep = "-" * label_w + "+"
        for m in minterms:
            sep += "-" * col_w + "+"
        sep += "-" * cov_w

        return header, sep

    def build_row(term, covered, col_w, label_w, cov_w):
        expr = term_to_expression(term, variables)
        row = expr.ljust(label_w) + "|"
        for m in minterms:
            if m in covered:
                row += "X".center(col_w) + "|"
            else:
                row += " " * col_w + "|"
        cov_str = ", ".join(str(x) for x in sorted(covered))
        row += cov_str.center(cov_w)
        return row

    # ── Glavna logika ────────────────────────────────────────────────────────

    col_w, label_w, cov_w = calculate_widths()
    header, sep = build_header(col_w, label_w, cov_w)

    print("\n=== TABLICA PRIMARNIH IMPLIKANTA ===")
    print(header)
    print(sep)

    for term, covered in prime_implicants:
        print(build_row(term, covered, col_w, label_w, cov_w))

    print()

def find_essential_prime_implicants(minterms: list[int], prime_implicants: list):
    """
    Pronalazi esencijalne primarne implikante — one koji jedini pokrivaju neki minterm.

    Args:
        minterms: lista minterma funkcije
        prime_implicants: lista tuplova (binarni_string, lista_minterma)

    Returns:
        Tuple (essential_indices, covered) gdje je essential_indices lista indeksa
        esencijalnih PI-ja, a covered lista svih minterma koje oni pokrivaju.
    """

    def find_covering_pis(m):
        """Vraća listu indeksa PI-ja koji pokrivaju minterm m."""
        covering = []
        for i in range(len(prime_implicants)):
            if m in prime_implicants[i][1]:
                covering.append(i)
        return covering

    def mark_as_essential(idx, essential_indices, covered):
        """Dodaje PI na listu esencijalnih i bilježi sve minterme koje pokriva."""
        if idx not in essential_indices:
            essential_indices.append(idx)
            for x in prime_implicants[idx][1]:
                if x not in covered:
                    covered.append(x)

    # ── Glavna logika ────────────────────────────────────────────────────────

    essential_indices = []
    covered = []

    for m in minterms:
        covering_pis = find_covering_pis(m)
        if len(covering_pis) == 1:
            mark_as_essential(covering_pis[0], essential_indices, covered)

    return essential_indices, covered

def petricks_method(minterms: list[int], prime_implicants: list, covered: list[int], essential_indices: list[int]):
    """
    Rješava problem pokrivanja preostalih minterma korištenjem Petrickove metode.
    
    Kada esencijalni primarni implikanti ne pokriju sve minterme funkcije, ova metoda 
    formira logički izraz (Produkt suma - POS) koji predstavlja sve moguće načine 
    pokrivanja. Množenjem tog izraza i primjenom pravila Booleove algebre (idempotentnost 
    i apsorpcija), metoda pronalazi sve minimalne i hardverski najjeftinije kombinacije 
    dodatnih primarnih implikanata.

    Args:
        minterms: Lista svih zadanih minterma funkcije.
        prime_implicants: Lista svih pronađenih primarnih implikanata.
        covered: Lista minterma koji su već pokriveni esencijalnim implikantima.
        essential_indices: Lista indeksa esencijalnih primarnih implikanata.

    Returns:
        Lista listi (ili jedna lista) indeksa primarnih implikanata koji predstavljaju 
        optimalno(a) rješenje(a) za pokrivanje preostalih minterma.
    """
    def find_uncovered():
        """Vraća listu minterma koji nisu pokriveni esencijalnim implikantima."""
        uncovered = []
        for m in minterms:
            if m not in covered:
                uncovered.append(m)
        return uncovered

    def pis_covering(m):
        """Kreira Produkt suma (POS): listu listi svih neesencijalnih PI-ja koji pokrivaju svaki minterm."""
        covering = []
        for i in range(len(prime_implicants)):
            if m in prime_implicants[i][1] and i not in essential_indices:
                covering.append([i])
        if len(covering) == 0:
            raise ValueError(f"Greška: Minterm {m} se ne može pokriti.")
        return covering

    def merge(x, y):
        """Spaja dvije liste indeksa i uklanja duplikate (Zakon idempotentnosti: A * A = A)."""
        return sorted(set(x + y))

    def is_redundant(c1, result):
        """Provjerava je li izraz nadskup postojećeg izraza (Zakon apsorpcije: A + AB = A)."""
        for c2 in result:
            if c1 != c2 and len(c2) < len(c1) and all(item in c1 for item in c2):
                return True
        return False

    def multiply(a, b):
        """Množi dvije zagrade (SOP izraze) primjenjujući Booleova pravila za minimizaciju."""
        result = []
        for x in a:
            for y in b:
                combined = merge(x, y)
                if combined not in result:
                    result.append(combined)

        # Čišćenje redundantnih kombiacija absorpcijom
        absorbed = []
        for c in result:
            if not is_redundant(c, result):
                absorbed.append(c)
        return absorbed

    def count_cost(c):
        """Računa hardversku cijenu kombinacije: vraća par (broj_implikanata, broj_literala)."""
        num_lit = 0
        for idx in c:
            for char in prime_implicants[idx][0]:
                if char == '0' or char == '1':
                    num_lit += 1
        return (len(c), num_lit)  # (broj PI-ja, broj literala)

    def find_best_covers(cover):
        """Iz niza svih valjanih covera pronalazi one s najmanjom hardverskom cijenom."""
        min_cost = min(count_cost(c) for c in cover)  # tuple usporedba: prvo pis, pa lit
        best = []
        for c in cover:
            if count_cost(c) == min_cost and c not in best:
                best.append(c)
        return best

    # ── Glavna logika ────────────────────────────────────────────────────────

    uncovered = find_uncovered()
    if len(uncovered) == 0:
        return [[]]

    print("\n=== PETRICKOVA METODA ===")
    print(f"Nepokriveni mintermi: {uncovered}")

    cover = pis_covering(uncovered[0])
    for m in uncovered[1:]:
        cover = multiply(cover, pis_covering(m))

    best_covers = find_best_covers(cover)
    print(f"Minimalni pokrivači (dodatni PI-ji uz esencijalne): {best_covers}")
    return best_covers