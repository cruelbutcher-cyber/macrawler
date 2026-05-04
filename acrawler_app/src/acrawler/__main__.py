#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
zcrawler.py – Enhanced Web Crawler with Tkinter GUI
Searches for specified keywords in URLs, content, and redirects on a website.
Features:
- Web scraping with BeautifulSoup
- Multi-threaded crawling with configurable modes
- Tkinter GUI for user interaction
- CSV export of results
"""
import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
import requests
from bs4 import BeautifulSoup, FeatureNotFound
from urllib.parse import urljoin, urlparse, parse_qs, unquote, quote, urlunparse
from collections import deque
import csv
import datetime
import re
import time
from io import StringIO
import json
import hashlib
import html
import logging
import tldextract
from urllib3.util import Retry
from requests.adapters import HTTPAdapter
import threading

# Verify required third-party libraries are available
for _lib in ('requests', 'bs4', 'tldextract'):
    try:
        __import__(_lib)
    except ImportError:
        print(f"Error: Missing library '{_lib}'. Install it with: pip install {_lib}")
        exit(1)

class EnhancedWebCrawler:
    def __init__(self, start_url, crawl_mode="Standard", keywords=None, status_callback=None, progress_callback=None):
        self.session = self._create_session()
        self.start_url = start_url
        self.keywords = keywords if keywords else ["gowithguide", "go with guide", "go-with-guide"]
        self.main_domain = urlparse(start_url).netloc
        self.crawl_mode = crawl_mode
        self.max_pages = {"Quick": 5, "Standard": 150, "Complete": 5000}[crawl_mode]
        self.visited = set()
        self.results = []
        self.queue = deque([start_url])
        self.categories = []
        self.current_category = None
        self.status_messages = []
        self.user_stopped = False
        self.pages_crawled = 0
        self.redirect_cache = {}
        self.internal_links = set()
        self.known_shorteners = [
            'bit.ly', 'tinyurl.com', 'goo.gl', 't.co', 'ow.ly', 'is.gd',
            'buff.ly', 'adf.ly', 'bit.do', 'mcaf.ee', 'su.pr', 'tiny.cc',
            'tidd.ly', 'redirectingat.com', 'go.redirectingat.com', 'go.skimresources.com'
        ]
        self.awin_domains = ['awin1.com', 'zenaps.com']
        self.potential_affiliate_domains = [
            'track.', 'go.', 'click.', 'buy.', 'shop.', 'link.', 'visit.',
            'affiliate.', 'partners.', 'tracking.', 'redirect.', 'ref.'
        ]
        self.potential_affiliate_paths = [
            '/visit', '/go', '/goto', '/redirect', '/click', '/buy', '/shop',
            '/link', '/affiliate', '/partner', '/tracking', '/ref', '/out'
        ]
        self.potential_affiliate_params = [
            'site', 'url', 'link', 'goto', 'target', 'redirect', 'redirect_to',
            'dest', 'destination', 'u', 'to', 'out', 'away', 'href'
        ]
        self.crawled_pages_content = {}
        self.url_fragments_checked = set()
        self.status_callback = status_callback
        self.progress_callback = progress_callback
        self.setup_logger()
    
    def setup_logger(self):
        self.logger = logging.getLogger('crawler')
        self.logger.setLevel(logging.INFO)
        if not self.logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            self.logger.addHandler(handler)
    
    def _create_session(self):
        session = requests.Session()
        retries = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"]
        )
        adapter = HTTPAdapter(max_retries=retries)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Connection': 'keep-alive',
            'Upgrade-Insecure-Requests': '1',
            'Cache-Control': 'max-age=0'
        })
        return session
    
    def get_soup(self, html_content):
        try:
            return BeautifulSoup(html_content, 'lxml')
        except FeatureNotFound:
            self.status_messages.append("Warning: 'lxml' parser not found. Using 'html.parser' instead.")
            if self.status_callback:
                self.status_callback("Warning: 'lxml' parser not found. Using 'html.parser' instead.")
            return BeautifulSoup(html_content, 'html.parser')
    
    def is_same_domain(self, url):
        main_domain_parts = tldextract.extract(self.start_url)
        url_domain_parts = tldextract.extract(url)
        return (main_domain_parts.domain == url_domain_parts.domain and
                main_domain_parts.suffix == url_domain_parts.suffix)
    
    def is_subdomain_of(self, url_netloc):
        main_domain = self.main_domain.replace("www.", "").lower()
        url_netloc = url_netloc.replace("www.", "").lower()
        return url_netloc.endswith("." + main_domain) or url_netloc == main_domain
    
    def is_relevant_path(self, url):
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        if re.search(r'\.(jpg|jpeg|png|gif|svg|pdf|zip|rar|css|js|xml|json)$', path):
            return False
        if re.search(r'/(login|logout|register|signin|signout|cart|checkout|privacy|terms)/?$', path):
            return False
        if re.search(r'/(post|article|blog|news|story|travel|guide|destination|affiliate)/', path):
            return True
        if len(parse_qs(parsed_url.query)) > 3:
            return False
        return True
    
    def normalize_url(self, url):
        parsed = urlparse(url)
        normalized = urlunparse((parsed.scheme, parsed.netloc, parsed.path,
                                parsed.params, parsed.query, ''))
        if normalized.endswith('/'):
            normalized = normalized[:-1]
        return normalized
    
    def looks_like_affiliate_url(self, url):
        url_lower = url.lower()
        parsed_url = urlparse(url_lower)
        netloc = parsed_url.netloc
        path = parsed_url.path
        
        # Check for known shorteners
        if any(shortener in netloc for shortener in self.known_shorteners):
            return True
        
        # Check for potential affiliate domains
        if any(tracker in netloc for tracker in self.potential_affiliate_domains):
            return True
        
        # Check for Awin domains with merchant ID
        if any(domain in netloc for domain in self.awin_domains):
            query_params = parse_qs(parsed_url.query)
            if 'v' in query_params and query_params['v'][0] == '87121':
                return True
            if 'awinmid' in query_params and query_params['awinmid'][0] == '87121':
                return True
        
        # Check for potential affiliate paths
        if any(aff_path in path for aff_path in self.potential_affiliate_paths):
            return True
        
        # Check for affiliate parameters
        query_params = parse_qs(parsed_url.query)
        affiliate_params = ['aff', 'affid', 'affiliateid', 'ref', 'refid', 'referral',
                           'referralid', 'partner', 'partnerId', 'utm_source']
        for param in affiliate_params:
            if param in query_params:
                return True
        
        # Check for redirect parameters with target domains
        for param in self.potential_affiliate_params:
            if param in query_params:
                param_value = query_params[param][0].lower()
                if any(keyword in param_value for keyword in self.keywords):
                    return True
        
        # Check for tracking parameters
        tracking_params = ['utm_', 'ref', 'aff', 'source', 'campaign', 'medium']
        tracking_count = sum(1 for param in query_params if any(t in param for t in tracking_params))
        if tracking_count >= 2:
            return True
        
        # Check for awc parameter with merchant ID
        if 'awc' in query_params:
            awc_value = query_params['awc'][0]
            if '87121' in awc_value:
                return True
        
        return False
    
    def extract_redirection_url(self, html_content, url):
        soup = self.get_soup(html_content)
        redirect_urls = []
        meta_refresh = soup.find('meta', attrs={'http-equiv': re.compile('^refresh$', re.I)})
        if meta_refresh and meta_refresh.get('content'):
            match = re.search(r'url=(.+)', meta_refresh['content'], re.I)
            if match:
                redirect_url = match.group(1).strip()
                redirect_urls.append(urljoin(url, redirect_url))
        script_patterns = [
            r'window\.location(?:\.href)?\s*=\s*[\'"](.+?)[\'"]',
            r'window\.location\.replace\([\'"](.+?)[\'"]\)',
            r'window\.open\([\'"](.+?)[\'"]\)',
            r'location\.href\s*=\s*[\'"](.+?)[\'"]',
            r'location\.replace\([\'"](.+?)[\'"]\)',
            r'setTimeout\([\'"]window\.location\.href=[\'"](.+?)[\'"][\'"]',
            r'url:\s*[\'"](.+?)[\'"]',
            r'href=[\'"](.+?)[\'"]'
        ]
        scripts = soup.find_all('script')
        for script in scripts:
            if script.string:
                for pattern in script_patterns:
                    matches = re.findall(pattern, script.string)
                    for match in matches:
                        if len(match) > 10:
                            redirect_urls.append(urljoin(url, match))
        parsed_url = urlparse(url)
        query_params = parse_qs(parsed_url.query)
        redirect_params = ['redirect_to', 'redirect', 'url', 'link', 'goto', 'target', 'ued']
        for param in redirect_params:
            if param in query_params:
                decoded_url = unquote(query_params[param][0])
                redirect_urls.append(urljoin(url, decoded_url))
        return redirect_urls
    
    def check_url_for_keywords(self, url, source_url):
        if not url or not isinstance(url, str):
            return
        url_hash = hashlib.md5(url.encode()).hexdigest()
        if url_hash in self.url_fragments_checked:
            return
        self.url_fragments_checked.add(url_hash)
        matched_kws = self.get_matched_keywords(url)
        if matched_kws:
            self.add_result(
                source_url=source_url,
                matched_url=url,
                element='url',
                attribute='href',
                content=url,
                keywords=matched_kws,
                location_type='direct_url'
            )
        if self.looks_like_affiliate_url(url):
            final_url, history = self.resolve_redirects(url)
            if final_url != url:
                matched_kws_final = self.get_matched_keywords(final_url)
                if matched_kws_final:
                    self.add_result(
                        source_url=source_url,
                        matched_url=final_url,
                        element='url',
                        attribute='href',
                        content=f"Redirected from: {url} to: {final_url}",
                        keywords=matched_kws_final,
                        location_type='redirected_url'
                    )
            for intermediate_url in history:
                matched_kws_intermediate = self.get_matched_keywords(intermediate_url)
                if matched_kws_intermediate:
                    self.add_result(
                        source_url=source_url,
                        matched_url=intermediate_url,
                        element='url',
                        attribute='href',
                        content=f"Redirect chain URL: {intermediate_url}",
                        keywords=matched_kws_intermediate,
                        location_type='redirect_chain_url'
                    )
    
    def get_matched_keywords(self, text):
        if not text or not isinstance(text, str):
            return []
        matched = []
        text_lower = text.lower()
        for keyword in self.keywords:
            if keyword.lower() in text_lower:
                matched.append(keyword)
        return matched
    
    def add_result(self, source_url, matched_url, element, attribute, content, keywords, location_type):
        result = {
            'source_url': source_url,
            'matched_url': matched_url,
            'keyword': ', '.join(keywords),
            'location_type': location_type,
            'element': element,
            'attribute': attribute,
            'content': content,
            'timestamp': datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        }
        self.results.append(result)
        if self.status_callback:
            self.status_callback(f"Found match: {matched_url} (Keyword: {result['keyword']})")
    
    def resolve_redirects(self, url):
        if url in self.redirect_cache:
            return self.redirect_cache[url]
        history = []
        final_url = url
        try:
            response = self.session.head(url, allow_redirects=True, timeout=5)
            if response.history:
                history = [resp.url for resp in response.history]
                final_url = response.url
            self.redirect_cache[url] = (final_url, history)
        except requests.RequestException:
            self.redirect_cache[url] = (url, [])
        return self.redirect_cache[url]
    
    def process_url(self, url):
        if url in self.visited or self.pages_crawled >= self.max_pages or not url or self.user_stopped:
            return []
        self.visited.add(url)
        self.pages_crawled += 1
        if self.progress_callback:
            self.progress_callback(self.pages_crawled / self.max_pages)
        try:
            response = self.session.get(
                url,
                headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                    'Accept': 'text/html,application/xhtml+xml,application/xml'
                },
                timeout=20,
                allow_redirects=True
            )
            response.raise_for_status()
            content_type = response.headers.get('content-type', '').lower()
            if 'text/html' not in content_type:
                return []
            html_content = response.text
            self.crawled_pages_content[url] = html_content
            soup = self.get_soup(html_content)
            matched_kws = self.get_matched_keywords(html_content)
            if matched_kws:
                self.add_result(
                    source_url=url,
                    matched_url=url,
                    element='page_content',
                    attribute='text',
                    content=html_content[:200],
                    keywords=matched_kws,
                    location_type='content'
                )
            redirect_urls = self.extract_redirection_url(html_content, url)
            for redirect_url in redirect_urls:
                self.check_url_for_keywords(redirect_url, url)
            links = []
            for a_tag in soup.find_all('a', href=True):
                href = a_tag.get('href')
                if not href:
                    continue
                absolute_url = urljoin(url, href)
                absolute_url = self.normalize_url(absolute_url)
                if (self.is_same_domain(absolute_url) or self.is_subdomain_of(urlparse(absolute_url).netloc)) and self.is_relevant_path(absolute_url):
                    links.append(absolute_url)
                    self.internal_links.add(absolute_url)
                self.check_url_for_keywords(absolute_url, url)
            return links
        except requests.RequestException as e:
            status_code = e.response.status_code if (e.response is not None) else None
            error_message = self.get_user_friendly_error(status_code, url)
            self.logger.warning(error_message)
            if self.status_callback:
                self.status_callback(error_message)
            return []
    
    def get_user_friendly_error(self, status_code, url):
        error_messages = {
            400: "Bad Request",
            401: "Unauthorized",
            403: "Forbidden",
            404: "URL not found",
            500: "Internal Server Error",
            502: "Bad Gateway",
            503: "Service Unavailable",
            504: "Gateway Timeout",
        }
        if status_code is None:
            message = "Connection error"
        else:
            message = error_messages.get(status_code, f"HTTP {status_code}")
        return f"{message} for URL: {url}"
    
    def start_crawling(self):
        self.reset_state()
        if self.status_callback:
            self.status_callback(f"Starting crawl of {self.start_url} in {self.crawl_mode} mode")
        while self.queue and not self.user_stopped and self.pages_crawled < self.max_pages:
            url = self.queue.popleft()
            new_urls = self.process_url(url)
            for new_url in new_urls:
                if (new_url not in self.visited and new_url not in self.queue and
                        self.pages_crawled < self.max_pages):
                    self.queue.append(new_url)
            if self.progress_callback:
                self.progress_callback(min(self.pages_crawled / self.max_pages, 1.0))
            if self.results:
                if self.status_callback:
                    self.status_callback(f"Found {len(self.results)} matches")
        if self.status_callback:
            self.status_callback("Crawling completed")
        return self.results
    
    def reset_state(self):
        self.visited = set()
        self.queue = deque([self.start_url])
        self.results = []
        self.pages_crawled = 0
        self.redirect_cache = {}
        self.internal_links = set()
        self.crawled_pages_content = {}
        self.url_fragments_checked = set()

def generate_csv(results):
    csv_file = StringIO()
    writer = csv.DictWriter(csv_file, fieldnames=[
        'source_url', 'matched_url', 'keyword',
        'location_type', 'element', 'attribute',
        'content_sample', 'timestamp'
    ])
    writer.writeheader()
    for result in results:
        writer.writerow({
            'source_url': result['source_url'],
            'matched_url': result['matched_url'],
            'keyword': result['keyword'],
            'location_type': result['location_type'],
            'element': result['element'],
            'attribute': result['attribute'],
            'content_sample': result['content'][:300] if result['content'] else '',
            'timestamp': result['timestamp']
        })
    return csv_file.getvalue()

class WebCrawlerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Enhanced Web Crawler")
        self.root.geometry("900x700")
        self.crawler = None
        self.crawling_thread = None
        self.results = []
        self.create_widgets()
    
    def create_widgets(self):
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        title_label = ttk.Label(main_frame, text="Enhanced Web Crawler", font=('Helvetica', 16, 'bold'))
        title_label.pack(pady=10)
        instructions = ttk.Label(main_frame, text="Select keyword from the dropdown menu, then enter URL and press 'Run' button.", font=('Helvetica', 10))
        instructions.pack(pady=5)
        input_frame = ttk.Frame(main_frame)
        input_frame.pack(fill=tk.X, pady=10)
        url_label = ttk.Label(input_frame, text="Website URL:")
        url_label.grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.url_entry = ttk.Entry(input_frame, width=50)
        self.url_entry.grid(row=0, column=1, padx=5, pady=5)
        self.url_entry.insert(0, "https://example.com")
        keyword_label = ttk.Label(input_frame, text="Keyword:")
        keyword_label.grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        self.keyword_var = tk.StringVar()
        self.keyword_var.set("gowithguide, go with guide, go-with-guide")
        self.keyword_combobox = ttk.Combobox(input_frame, textvariable=self.keyword_var, width=47)
        self.keyword_combobox['values'] = (
            "gowithguide, go with guide, go-with-guide",
            "Custom"
        )
        self.keyword_combobox.grid(row=1, column=1, padx=5, pady=5)
        self.keyword_combobox.bind("<<ComboboxSelected>>", self.on_keyword_select)
        self.custom_keyword_frame = ttk.Frame(input_frame)
        custom_keyword_label = ttk.Label(self.custom_keyword_frame, text="Custom Keyword:")
        custom_keyword_label.grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.custom_keyword_entry = ttk.Entry(self.custom_keyword_frame, width=47)
        self.custom_keyword_entry.grid(row=0, column=1, padx=5, pady=5)
        mode_label = ttk.Label(input_frame, text="Crawl Mode:")
        mode_label.grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        self.mode_var = tk.StringVar()
        self.mode_var.set("Standard")
        mode_combobox = ttk.Combobox(input_frame, textvariable=self.mode_var, width=47)
        mode_combobox['values'] = ("Quick", "Standard", "Complete")
        mode_combobox.grid(row=2, column=1, padx=5, pady=5)
        buttons_frame = ttk.Frame(main_frame)
        buttons_frame.pack(fill=tk.X, pady=10)
        self.run_button = ttk.Button(buttons_frame, text="Run", command=self.start_crawling)
        self.run_button.pack(side=tk.LEFT, padx=5)
        self.stop_button = ttk.Button(buttons_frame, text="Stop", command=self.stop_crawling, state=tk.DISABLED)
        self.stop_button.pack(side=tk.LEFT, padx=5)
        self.save_button = ttk.Button(buttons_frame, text="Save Results", command=self.save_results, state=tk.DISABLED)
        self.save_button.pack(side=tk.LEFT, padx=5)
        status_frame = ttk.LabelFrame(main_frame, text="Status", padding="10")
        status_frame.pack(fill=tk.X, pady=10)
        self.status_var = tk.StringVar()
        self.status_var.set("Idle")
        status_label = ttk.Label(status_frame, textvariable=self.status_var)
        status_label.pack(side=tk.LEFT, padx=5)
        self.progress = ttk.Progressbar(status_frame, orient=tk.HORIZONTAL, length=300, mode='determinate')
        self.progress.pack(side=tk.RIGHT, padx=5)
        results_frame = ttk.LabelFrame(main_frame, text="Results", padding="10")
        results_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        self.results_text = scrolledtext.ScrolledText(results_frame, wrap=tk.WORD, width=80, height=15)
        self.results_text.pack(fill=tk.BOTH, expand=True)
        self.results_count_var = tk.StringVar()
        self.results_count_var.set("Matches found: 0")
        results_count_label = ttk.Label(results_frame, textvariable=self.results_count_var)
        results_count_label.pack(pady=5)
    
    def on_keyword_select(self, event):
        if self.keyword_var.get() == "Custom":
            self.custom_keyword_frame.grid(row=3, column=0, columnspan=2, sticky=tk.W, padx=5, pady=5)
        else:
            self.custom_keyword_frame.grid_forget()
    
    def get_keywords(self):
        if self.keyword_var.get() == "Custom":
            custom_keyword = self.custom_keyword_entry.get().strip()
            if custom_keyword:
                return [custom_keyword]
            else:
                messagebox.showwarning("Warning", "Please enter a custom keyword.")
                return None
        else:
            return ["gowithguide", "go with guide", "go-with-guide"]
    
    def start_crawling(self):
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showwarning("Warning", "Please enter a URL.")
            return
        
        parsed = urlparse(url)
        if not parsed.scheme:
            url = f'https://{url}'
        elif parsed.scheme not in ('http', 'https'):
            messagebox.showwarning("Warning", "URL must start with http:// or https://")
            return
        self.url_entry.delete(0, tk.END)
        self.url_entry.insert(0, url)
        
        keywords = self.get_keywords()
        if not keywords:
            return
        
        mode = self.mode_var.get()
        
        self.results_text.delete(1.0, tk.END)
        self.results_count_var.set("Matches found: 0")
        self.results = []
        self.status_var.set("Running")
        self.run_button.config(state=tk.DISABLED)
        self.stop_button.config(state=tk.NORMAL)
        self.save_button.config(state=tk.DISABLED)
        self.progress['value'] = 0
        
        self.crawler = EnhancedWebCrawler(
            start_url=url,
            crawl_mode=mode,
            keywords=keywords,
            status_callback=self.update_status,
            progress_callback=self.update_progress
        )
        
        self.crawling_thread = threading.Thread(target=self.run_crawler)
        self.crawling_thread.daemon = True
        self.crawling_thread.start()
    
    def run_crawler(self):
        try:
            self.results = self.crawler.start_crawling()
            self.root.after(0, self.crawling_complete)
        except Exception as e:
            self.root.after(0, lambda e=e: self.crawling_error(str(e)))
    
    def crawling_complete(self):
        self.status_var.set("Completed")
        self.run_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        
        if self.results:
            self.save_button.config(state=tk.NORMAL)
            self.results_count_var.set(f"Matches found: {len(self.results)}")
            self.display_results()
        else:
            self.results_count_var.set("Matches found: 0")
            self.results_text.insert(tk.END, "No matches found.\n")
    
    def crawling_error(self, error_msg):
        self.status_var.set("Error")
        self.run_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        self.results_text.insert(tk.END, f"Error: {error_msg}\n")
    
    def stop_crawling(self):
        if self.crawler:
            self.crawler.user_stopped = True
            self.crawler.queue.clear()  # Clear the queue to stop processing
        self.status_var.set("Stopped")
        self.run_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        
        if self.results:
            self.save_button.config(state=tk.NORMAL)
            self.results_count_var.set(f"Matches found: {len(self.results)}")
            self.display_results()
    
    def update_status(self, message):
        self.root.after(0, lambda: self.results_text.insert(tk.END, f"{message}\n"))
        self.root.after(0, lambda: self.results_text.see(tk.END))
    
    def update_progress(self, value):
        self.root.after(0, lambda: self.progress.config(value=value * 100))
    
    def display_results(self):
        self.results_text.delete(1.0, tk.END)
        for i, result in enumerate(self.results, 1):
            self.results_text.insert(tk.END, f"Match {i}:\n")
            self.results_text.insert(tk.END, f"Source URL: {result['source_url']}\n")
            self.results_text.insert(tk.END, f"Matched URL: {result['matched_url']}\n")
            self.results_text.insert(tk.END, f"Keyword: {result['keyword']}\n")
            self.results_text.insert(tk.END, f"Location Type: {result['location_type']}\n")
            self.results_text.insert(tk.END, f"Element: {result['element']} [{result['attribute']}]\n")
            if result['content']:
                content_preview = result['content'][:100] + ('...' if len(result['content']) > 100 else '')
                self.results_text.insert(tk.END, f"Content: {content_preview}\n")
            self.results_text.insert(tk.END, "-" * 80 + "\n")
    
    def save_results(self):
        if not self.results:
            messagebox.showinfo("Info", "No results to save.")
            return
        
        csv_data = generate_csv(self.results)
        file_path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
            initialfile=f"crawl_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', newline='') as f:
                    f.write(csv_data)
                messagebox.showinfo("Success", f"Results saved to {file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save results: {str(e)}")

def main():
    root = tk.Tk()
    app = WebCrawlerGUI(root)
    root.mainloop()

if __name__ == "__main__":
    main()

